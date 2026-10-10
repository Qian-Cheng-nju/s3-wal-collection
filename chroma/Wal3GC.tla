----------------------------- MODULE Wal3GC -----------------------------

EXTENDS Wal3Common

(* WAL garbage collection, three phases: 
    1. Publish or reuse a plan (GARBAGE file in impl)
    2. Trim the manifest fragment refs
    3. Delete fragments  
*)

\* ****************************************************
\* WAL GC ACTIONS
\* ****************************************************

(* ---------------------------------------------------------
    ACTION: GcPhase1ReadCursor

    DESC TODO
-----------------------------------------------------------*)

\* The replica GC is idle, or we restart a GC that experienced
\* aborted due to a conflict and there are no other
\* functional GC tasks. This allows us to bound the
\* number of GC retries while guaranteeing one
\* will finish (we avoid infinite GC battles).
InTriggerableState(r) ==
    \/ rGcState[r] = IDLE
    \/ /\ rGcState[r] = ABORTED
       /\ ~\E r0 \in Replicas : rGcState[r0] \notin {ABORTED, PREEMPTED}

\* This is not the protocol, just some state space reduction.
\* The compaction cursor covers the WAL seqNo range.
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

    DESC TODO
-----------------------------------------------------------*)

GcPhase1ReadGcFile(r) ==
    /\ rGcState[r] = GC_P1_READ_GC_FILE
    /\ rGcCachedPlan' = [rGcCachedPlan EXCEPT ![r] = gcPlanFile]
    /\ rGcState' = [rGcState EXCEPT ![r] = GC_P1_COMPUTE_PLAN]
    /\ UNCHANGED <<storeVars, auxVars, repSharedVars, repWriterVars, repCompVars,
                   rGcCompCursor, rGcPinnedPlan, rGcTrimLimit>>

(* ---------------------------------------------------------
    ACTION: GcPhase1ComputePlan

    DESC TODO
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
    /\ rGcCachedPlan[r].seqNoLimit >= CachedSeqNoFloor(r) + 1
    /\ rGcCachedPlan[r].seqNoLimit <= CachedSeqNoCeiling(r) + 1

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

    DESC TODO
-----------------------------------------------------------*)

GcPhase2ReadGcFile(r) ==
    /\ rGcState[r] = GC_P2_READ_GC_FILE
    /\ rGcCachedPlan' = [rGcCachedPlan EXCEPT ![r] = gcPlanFile]
    \* Phase 2 independently reloads the plan and serializes this replica's
    \* manifest update. The phase 1 plan remains pinned for phase 3 deletion.
    /\ rGcTrimLimit' = [rGcTrimLimit EXCEPT ![r] = gcPlanFile.seqNoLimit]
    /\ rManifestLocked' = [rManifestLocked EXCEPT ![r] = TRUE]
    /\ rGcState' = [rGcState EXCEPT ![r] = GC_P2_CAS_MANIFEST]
    /\ UNCHANGED <<storeVars, auxVars, rManifest, repWriterVars,
                   repCompVars, rGcCompCursor, rGcPinnedPlan>>

(* ---------------------------------------------------------
    ACTION: GcPhase2CasManifest

    DESC TODO
-----------------------------------------------------------*)

TrimmedFragRefs(r) ==
    LET limit == rGcTrimLimit[r]
        refs  == rManifest[r].fragRefs
        i     == CHOOSE i \in DOMAIN refs :
                    refs[i].seqNo = limit - 1
    IN IF i = Len(refs) THEN <<>>
       ELSE SubSeq(refs, i+1, Len(refs))

AbortInPhase2(r) ==
    /\ rGcState' = [rGcState EXCEPT ![r] = ABORTED]
    /\ rManifestLocked' = [rManifestLocked EXCEPT ![r] = FALSE]
    /\ UNCHANGED <<manifest, rManifest, rWriterState>>

AttemptCasWrite(r) ==
    \/ /\ rManifest[r].version /= manifest.version
       /\ rManifestLocked' = [rManifestLocked EXCEPT ![r] = FALSE]
       /\ PreemptWriterAndGc(r)
       /\ UNCHANGED <<manifest, rManifest>>
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

GcPhase2CasManifest(r) ==
    /\ rGcState[r] = GC_P2_CAS_MANIFEST
    /\ IF ~GcFileApplicable(r)
       THEN AbortInPhase2(r)
       ELSE AttemptCasWrite(r)
    /\ UNCHANGED <<fragments, checkpoint, compCursor, gcPlanFile, auxVars,
                   repCompVars, rWriterPendingValues, rWriterFragment,
                   rWriterNextPos, rWriterNextSeqNo, rGcCachedPlan,
                   rGcCompCursor, rGcPinnedPlan, rGcTrimLimit>>

(* ---------------------------------------------------------
    ACTION: GcPhase3ReadGcFile

    DESC TODO
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

    DESC TODO
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

    DESC TODO
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

    DESC TODO
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

=============================================================================
