----------------------------- MODULE Wal3GC -----------------------------

EXTENDS Wal3Common

(* WAL garbage collection, three phases: 
    1. Publish or reuse a plan (GARBAGE file in impl)
    2. Trim the manifest fragment refs
    3. Delete fragments  
*)

PlanApplicable(r, plan) ==
    /\ plan.seqNoLimit >= CachedSeqNoFloor(r) + 1
    /\ plan.seqNoLimit <= CachedSeqNoCeiling(r) + 1

\* ****************************************************
\* WAL GC ACTIONS
\* ****************************************************

(* ---------------------------------------------------------
    ACTION: GcPhase1ReadCursor

    A GC run starts by reading the compaction cursor,
    which bounds the prefix it may collect. 

    Note 1. Chroma has many cursors, but this spec only
    cares about the compaction cursor.

    Note 2. We control the conditions when GC can start 
    to avoid infinite battles between replicas (infinite
    state space) and to avoid GC that would stop early
    due to nothing to collect (that would also inflate
    the state space massively).
-----------------------------------------------------------*)

InTriggerableState(r) ==
    \/ rGcState[r] = IDLE
    \* ABORTED means a GC hit a retryable conflict. In this
    \* spec we limit retries to one replica at a time, else it
    \* causes infinite battles.
    \/ /\ rGcState[r] = ABORTED
       /\ ~\E r0 \in Replicas : rGcState[r0] \notin {ABORTED, PREEMPTED}

\* This is not the protocol, just some state space reduction.
CompactionCursorInWalRange(r) ==
    /\ CachedFloorLogPos(r) > 0
    /\ compCursor.pos >= CachedFloorLogPos(r)
    /\ compCursor.pos <= CachedCeilingLogPos(r)

GcPhase1ReadCursor(r) ==
    /\ InTriggerableState(r)
    /\ CompactionCursorInWalRange(r)
    /\ rGcCompCursor' = [rGcCompCursor EXCEPT ![r] = compCursor]
    /\ rGcPinnedPlan' = [rGcPinnedPlan EXCEPT ![r] = None]
    /\ rGcState' = [rGcState EXCEPT ![r] = GC_P1_READ_GC_FILE]
    /\ UNCHANGED <<storeVars, auxVars, repSharedVars, repWriterVars, 
                   repCompVars, rGcCachedPlan, rGcTrimLimit>>

(* ---------------------------------------------------------
    ACTION: GcPhase1ReadGcFile

    GC reads the current GC plan before choosing what 
    to collect. In the impl, this is the GARBAGE file.
-----------------------------------------------------------*)

GcPhase1ReadGcFile(r) ==
    /\ rGcState[r] = GC_P1_READ_GC_FILE
    /\ rGcCachedPlan' = [rGcCachedPlan EXCEPT ![r] = gcPlanFile]
    /\ rGcState' = [rGcState EXCEPT ![r] = GC_P1_COMPUTE_PLAN]
    /\ UNCHANGED <<storeVars, auxVars, repSharedVars, repWriterVars, repCompVars,
                   rGcCompCursor, rGcPinnedPlan, rGcTrimLimit>>

(* ---------------------------------------------------------
    ACTION: GcPhase1ComputePlan

    Now the GC has loaded the current plan file, it
    can take one of four sub-actions here:

    1. Stop: See there is nothing to collect and stop.
    2. Compute new plan: The existing plan is empty, 
       so compute and persist a new plan (to S3). Then
       move on to phase 2.
    3. Reuse plan: The existing plan is still valid,
       there remains GC work to do for this plan. Move
       on to phase 2.
    4. Reset plan: The existing plan is totally stale,
       so clear it, persist it and restart phase 1.

    (2) and (4) both pin GC plan, which is checked
    later in phase 3.
-----------------------------------------------------------*)

\* SUB-ACTION: StopEarly ----------------------------------

\* condition
NothingToCollect(r) ==
    LET firstToKeep == rGcCompCursor[r].pos + 1
        frag == rManifest[r].fragRefs
    IN ~\E i \in DOMAIN frag : frag[i].limit <= firstToKeep

\* action
StopEarly(r) ==
    /\ rGcState' = [rGcState EXCEPT ![r] = IDLE]
    /\ UNCHANGED <<gcPlanFile, rGcCachedPlan, rGcPinnedPlan>>

\* SUB-ACTION: SaveNewPlan --------------------------------

\* condition
GcFileEmpty(r) == rGcCachedPlan[r].seqNoLimit = 0

\* actions
ComputeGcLimit(r, pos) ==
    LET firstToKeep == rGcCompCursor[r].pos + 1
        frag == rManifest[r].fragRefs
        max  == CHOOSE i \in DOMAIN frag :
                    /\ frag[i].limit <= firstToKeep
                    /\ ~\E j \in DOMAIN frag :
                        /\ frag[j].limit <= firstToKeep
                        /\ j > i
    IN frag[max].seqNo + 1

GcFileMatch(r) ==
    \/ gcPlanFile = None
    \/ /\ rGcCachedPlan[r] /= None
       /\ rGcCachedPlan[r].version = gcPlanFile.version

SaveNewPlan(r) ==
    LET gcLimit   == ComputeGcLimit(r, rGcCompCursor[r])
        newGcFile == [seqNoLimit |-> gcLimit,
                      version    |-> gcPlanFile.version + 1]
    IN
        \/ /\ GcFileMatch(r)
           /\ gcPlanFile' = newGcFile
           /\ rGcCachedPlan' = [rGcCachedPlan EXCEPT ![r] = newGcFile]
           /\ rGcPinnedPlan' = [rGcPinnedPlan EXCEPT ![r] = newGcFile]
           /\ rGcState' = [rGcState EXCEPT ![r] = GC_P2_READ_GC_FILE]
        \/ /\ ~GcFileMatch(r)
           /\ rGcState' = [rGcState EXCEPT ![r] = ABORTED]
           /\ UNCHANGED <<gcPlanFile, rGcCachedPlan, rGcPinnedPlan>>

\* SUB-ACTION: ReuseExistingPlan ---------------------------

\* condition
GcFileApplicable(r) ==
    PlanApplicable(r, rGcCachedPlan[r])

\* action
ReusePlan(r) ==
    /\ rGcPinnedPlan' = [rGcPinnedPlan EXCEPT ![r] = rGcCachedPlan[r]]
    /\ rGcState' = [rGcState EXCEPT ![r] = GC_P2_READ_GC_FILE]
    /\ UNCHANGED <<gcPlanFile, rGcCachedPlan>>

\* SUB-ACTION: ResetPlan -----------------------------------

\* condition
GcFileNotApplicable(r) == ~GcFileApplicable(r)

\* action
ResetPlan(r) ==
    /\ IF rGcCachedPlan[r].version = gcPlanFile.version
       THEN gcPlanFile' = [seqNoLimit |-> 0,
                           version    |-> gcPlanFile.version + 1]
       ELSE UNCHANGED gcPlanFile
    /\ rGcState' = [rGcState EXCEPT ![r] = GC_P1_READ_GC_FILE]
    /\ UNCHANGED <<rGcCachedPlan, rGcPinnedPlan>>

\* Main action
GcPhase1ComputePlan(r) ==
    /\ rGcState[r] = GC_P1_COMPUTE_PLAN
    /\ IF NothingToCollect(r) THEN StopEarly(r)
       ELSE IF GcFileEmpty(r) THEN SaveNewPlan(r)
       ELSE IF GcFileApplicable(r) THEN ReusePlan(r)
       ELSE ResetPlan(r)
    /\ UNCHANGED <<manifest, fragments, checkpoint, compCursor,
                   auxVars, repSharedVars, repWriterVars, repCompVars,
                   rGcCompCursor, rGcTrimLimit>>


(* ---------------------------------------------------------
    ACTION: GcPhase2ReadGcFile

    GC reloads the GC plan file.
    If the plan is no longer applicable, GC aborts.
    Else, it locks the cached manifest for updates and
    the GC boundary stored in the plan is retained (rGcTrimLimit)

    Note: The impl serializes manifest updates (per replica) 
    a different way but a simple manifest lock works better
    for this spec. Basically replica-local GC and WAL writer
    can attempt to concurrently update and commit the manifest.
-----------------------------------------------------------*)

AbortInPhase2(r) ==
    /\ rGcState' = [rGcState EXCEPT ![r] = ABORTED]
    /\ rManifestLocked' = [rManifestLocked EXCEPT ![r] = FALSE]
    /\ UNCHANGED <<rGcCachedPlan, rGcTrimLimit>>

GcPhase2ReadGcFile(r) ==
    /\ rGcState[r] = GC_P2_READ_GC_FILE
    /\ IF ~PlanApplicable(r, gcPlanFile)
       THEN AbortInPhase2(r)
       ELSE /\ rGcCachedPlan' = [rGcCachedPlan EXCEPT ![r] = gcPlanFile]
            /\ rGcTrimLimit' = [rGcTrimLimit EXCEPT ![r] = gcPlanFile.seqNoLimit]
            /\ rManifestLocked' = [rManifestLocked EXCEPT ![r] = TRUE]
            /\ rGcState' = [rGcState EXCEPT ![r] = GC_P2_CAS_MANIFEST]
    /\ UNCHANGED <<storeVars, auxVars, rManifest, repWriterVars,
                   repCompVars, rGcCompCursor, rGcPinnedPlan>>

(* ---------------------------------------------------------
    ACTION: GcPhase2CasManifest

    GC removes fragment references below the trim GC boundary
    and attempts CAS the manifest in S3. A conflict preempts
    writer and GC; else it transitions to phase 3.
-----------------------------------------------------------*)

TrimmedFragRefs(r) ==
    LET limit == rGcTrimLimit[r]
        refs  == rManifest[r].fragRefs
        i     == CHOOSE i \in DOMAIN refs :
                    refs[i].seqNo = limit - 1
    IN IF i = Len(refs) THEN <<>>
       ELSE SubSeq(refs, i+1, Len(refs))

ManifestCasConflict(r) ==
    /\ rManifestLocked' = [rManifestLocked EXCEPT ![r] = FALSE]
    /\ PreemptWriterAndGc(r)
    /\ UNCHANGED <<manifest, rManifest>>

GcPhase2CasManifest(r) ==
    /\ rGcState[r] = GC_P2_CAS_MANIFEST
    /\ \/ /\ rManifest[r].version /= manifest.version
          /\ ManifestCasConflict(r)
       \/ /\ rManifest[r].version = manifest.version
          /\ LET m            == rManifest[r]
                 trimmed      == TrimmedFragRefs(r)
                 initialPos   == IF trimmed = <<>> THEN NextPos(m) ELSE m.initialPos
                 initialSeqNo == IF trimmed = <<>> THEN NextSeqNo(m) ELSE m.initialSeqNo
                 newManifest  == [fragRefs     |-> trimmed,
                                  initialPos   |-> initialPos,
                                  initialSeqNo |-> initialSeqNo,
                                  version      |-> m.version + 1]
             IN /\ manifest' = newManifest
                /\ rManifest' = [rManifest EXCEPT ![r] = newManifest]
                /\ rManifestLocked' = [rManifestLocked EXCEPT ![r] = FALSE]
                /\ rGcState' = [rGcState EXCEPT ![r] = GC_P3_READ_GC_FILE]
                /\ UNCHANGED rWriterState
    /\ UNCHANGED <<fragments, checkpoint, compCursor, gcPlanFile, auxVars,
                   repCompVars, rWriterPendingValues, rWriterFragment,
                   rWriterNextPos, rWriterNextSeqNo, rGcCachedPlan,
                   rGcCompCursor, rGcPinnedPlan, rGcTrimLimit>>

(* ---------------------------------------------------------
    ACTION: GcPhase3ReadGcFile

    GC rereads the plan file again from S3 and aborts if 
    its version no longer matches the plan pinned in phase 1.
-----------------------------------------------------------*)

GcPinnedPlanMatch(r) ==
    /\ rGcPinnedPlan[r] /= None
    /\ gcPlanFile /= None
    /\ rGcPinnedPlan[r].version = gcPlanFile.version

GcPhase3ReadGcFile(r) ==
    /\ rGcState[r] = GC_P3_READ_GC_FILE
    /\ rGcCachedPlan' = [rGcCachedPlan EXCEPT ![r] = gcPlanFile]
    /\ rGcState' = [rGcState EXCEPT ![r] = IF GcPinnedPlanMatch(r)
                                           THEN GC_P3_READ_MANIFEST
                                           ELSE ABORTED]
    /\ UNCHANGED <<storeVars, auxVars, repSharedVars, repWriterVars, repCompVars,
                   rGcCompCursor, rGcPinnedPlan, rGcTrimLimit>>

(* ---------------------------------------------------------
    ACTION: GcPhase3ReadManifest

    Before fragment delection can commence (state 
    GC_P3_DELETE), the GC reads the manifest from S3
    and checks that the pinned plan has been applied
    to the manifest. A race can occur here where
    one GC in Phase 1 can write a new plan, and another
    GC in phase 3 loads that plan before the other
    GC has trimmed the entries below the boundary.
    Without this check against the pinned plan, a
    GC can delete fragments still visible to readers.

    If the plan has been applied to the current manifest
    on S3, the GC transitions to GC_P3_DELETE, else
    it aborts.
-----------------------------------------------------------*)

GcPhase3ReadManifest(r) ==
    /\ rGcState[r] = GC_P3_READ_MANIFEST
    /\ rGcState' = [rGcState EXCEPT ![r] =
            IF PlanApplied(manifest, rGcPinnedPlan[r])
            THEN GC_P3_DELETE ELSE ABORTED]
    /\ UNCHANGED <<storeVars, auxVars, repSharedVars, repWriterVars, repCompVars,
                   rGcCachedPlan, rGcCompCursor, rGcPinnedPlan, rGcTrimLimit>>

(* ---------------------------------------------------------
    ACTION: GcPhase3Delete

    GC deletes one fragment below the pinned plan's boundary.
-----------------------------------------------------------*)

GcPhase3Delete(r) ==
    /\ rGcState[r] = GC_P3_DELETE
    /\ \E seqNo \in DOMAIN fragments :
        /\ seqNo < rGcPinnedPlan[r].seqNoLimit
        /\ fragments' = [sn \in (DOMAIN fragments \ {seqNo}) |->
                              fragments[sn]]
    /\ UNCHANGED <<manifest, checkpoint, compCursor, gcPlanFile,
                  auxVars, repSharedVars, repCompVars, repWriterVars, repGcVars>>

(* ---------------------------------------------------------
    ACTION: GcPhase3Complete

    After deleting the planned prefix, GC returns to idle.
    It clears the durable plan only if it still matches
    the pinned version.
-----------------------------------------------------------*)

GcPhase3Complete(r) ==
    /\ rGcState[r] = GC_P3_DELETE
    /\ ~\E seqNo \in DOMAIN fragments : seqNo < rGcPinnedPlan[r].seqNoLimit
    /\ IF GcPinnedPlanMatch(r)
       THEN /\ gcPlanFile' = [seqNoLimit |-> 0,
                              version    |-> gcPlanFile.version + 1]
            /\ rGcCachedPlan' = [rGcCachedPlan EXCEPT ![r] = None]
            /\ rGcCompCursor' = [rGcCompCursor EXCEPT ![r] = None]
       ELSE UNCHANGED <<gcPlanFile, rGcCachedPlan, rGcCompCursor>>
    /\ rGcState' = [rGcState EXCEPT ![r] = IDLE]
    /\ rGcPinnedPlan' = [rGcPinnedPlan EXCEPT ![r] = None]
    /\ UNCHANGED <<manifest, fragments, checkpoint, compCursor,
                  auxVars, repSharedVars, repCompVars, repWriterVars,
                  rGcTrimLimit>>

\* ****************************************************
\* Init, Next and Fairness
\* ****************************************************

GcInit ==
    /\ rGcState = [r \in Replicas |-> IDLE]
    /\ rGcCachedPlan = [r \in Replicas |-> None]
    /\ rGcPinnedPlan = [r \in Replicas |-> None]
    /\ rGcTrimLimit = [r \in Replicas |-> 0]
    /\ rGcCompCursor = [r \in Replicas |-> None]

GcNext(r) ==
    \/ GcPhase1ReadCursor(r)
    \/ GcPhase1ReadGcFile(r)
    \/ GcPhase1ComputePlan(r)
    \/ GcPhase2ReadGcFile(r)
    \/ GcPhase2CasManifest(r)
    \/ GcPhase3ReadGcFile(r)
    \/ GcPhase3ReadManifest(r)
    \/ GcPhase3Delete(r)
    \/ GcPhase3Complete(r)

GcFairness(r) ==
    /\ WF_vars(GcPhase1ReadCursor(r))
    /\ WF_vars(GcPhase1ReadGcFile(r))
    /\ WF_vars(GcPhase1ComputePlan(r))
    /\ WF_vars(GcPhase2ReadGcFile(r))
    /\ WF_vars(GcPhase2CasManifest(r))
    /\ WF_vars(GcPhase3ReadGcFile(r))
    /\ WF_vars(GcPhase3ReadManifest(r))
    /\ WF_vars(GcPhase3Delete(r))
    /\ WF_vars(GcPhase3Complete(r))

=============================================================================
