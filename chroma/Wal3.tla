----------------------------- MODULE Wal3 -------------------------

EXTENDS Naturals, Integers, FiniteSets, FiniteSetsExt, Sequences,
        SequencesExt, TLC

CONSTANTS Replicas, \* The set of replica processes
          Values    \* The set of values to append

\* Replica states
CONSTANTS IDLE, RECOVER, COMMIT_RECOVERED, REFRESH, READY,
          UPLOAD_FRAGMMENT, COMMIT_FRAGMENT,
          ILLEGAL_STATE, ABORT_WRITE, PREEMPTED,
          REPLAY_WAL, COMMIT_CHECKPOINT, READ_CURSOR, COMMIT_CURSOR,
          GC_P1_READ_GC_FILE, GC_P1_COMPUTE_PLAN, 
          GC_P2_READ_GC_FILE, GC_P2_CAS_MANIFEST, 
          GC_P3_READ_GC_FILE, GC_P3_DELETE 

CONSTANTS None, NotFound

\* Durable state on S3
VARIABLES manifest,      \* CAS protected leader state manifest file
          fragments,     \* Id -> Log entry file
          checkpoint,    \* very abstract published state storage (indexes etc)
          gcPlanFile,    \* GARBAGE file
          compCursor     \* Compaction cursor

\* WAL writer (appends) state
VARIABLES rWalState,        \* Replica -> current state
          rWalStaging,      \* Replica -> Staging data, incl manifest
          rWalPendingValues \* Replica -> Values pending commit

\* WAL GC task state
VARIABLES rGcState,         \* Replica -> current state
          rGcPlanFile,      \* Replica -> cached GC plan file (GARBAGE)
          rGcCompCursor     \* Replica -> cached compaction cursor

\* Compaction state
VARIABLES rCompState,       \* Replica -> current state
          rCompCheckpoint,  \* Replica -> cached checkpoint
          rCompCursor       \* Replica -> cached compaction cursor
          
VARIABLES auxUsedValues,    
          auxCommitted \* Successful write history         

storeVars == <<manifest, fragments, checkpoint, compCursor,
               gcPlanFile>>
repWalVars == <<rWalState, rWalStaging, rWalPendingValues>>
repGcVars == <<rGcState, rGcPlanFile, rGcCompCursor>>
repCompVars == <<rCompState, rCompCheckpoint, rCompCursor>>
replicaVars == <<repWalVars, repGcVars, repCompVars>>
auxVars == <<auxUsedValues, auxCommitted>>
vars == <<storeVars, replicaVars, auxVars>>

Symmetry ==
      Permutations(Replicas)
          \union Permutations(Values)

\* ****************************************************
\* HELPERS
\* ****************************************************

CachedManifest(r) == rWalStaging[r].manifest

NextPos(m) ==
    IF m.fragments = <<>> THEN m.initialPos
    ELSE Last(m.fragments).limit

NextSeqNo(m) ==
    IF m.fragments = <<>> THEN m.initialSeqNo
    ELSE Last(m.fragments).seqNo + 1

SetStagingFromManifest(r, m) ==
    [manifest  |-> m,
     fragment  |-> None, 
     nextPos   |-> NextPos(m),
     nextSeqNo |-> NextSeqNo(m),
     gcLimit   |-> IF rWalStaging[r] = None THEN 0
                   ELSE rWalStaging[r].gcLimit,
     locked    |-> FALSE]

ManifestSeqNoFloor(r) ==
    IF CachedManifest(r).fragments = <<>> THEN 0
    ELSE Head(CachedManifest(r).fragments).seqNo

ManifestSeqNoCeiling(r) ==
    IF CachedManifest(r).fragments = <<>> THEN 0
    ELSE Last(CachedManifest(r).fragments).seqNo    

MinPos(entries) == Head(entries).pos
MaxPos(entries) == Last(entries).pos

ManifestPosFloor(r) ==
    IF CachedManifest(r).fragments = <<>> THEN 0
    ELSE Head(CachedManifest(r).fragments).start

LocalCheckpointPos(r) == 
    IF rCompCheckpoint[r].snapshot = <<>> THEN 0
    ELSE Last(rCompCheckpoint[r].snapshot).pos

\* staging.locked is a way of this spec serializing manifest updates
IsManifestLocked(r) ==
    /\ rWalStaging[r] /= None
    /\ rWalStaging[r].locked = TRUE

\* Build a fragment ref from a fragment
FragRef(frag) ==
    [seqNo |-> frag.seqNo,
     start |-> MinPos(frag.entries),
     limit |-> MaxPos(frag.entries) + 1]

CommitFragment(r) ==
    LET m         == CachedManifest(r)
        f         == rWalStaging[r].fragment
        fragRef   == FragRef(f)
        manifest0 == [m EXCEPT !.fragments = Append(@, fragRef),
                               !.version   = @ + 1]
    IN
        /\ manifest' = manifest0
        /\ rWalStaging' = [rWalStaging EXCEPT ![r] = 
                                SetStagingFromManifest(r, manifest0)]
        /\ auxCommitted' = auxCommitted \o f.entries

NoCommit == UNCHANGED <<manifest, rWalStaging, auxCommitted>>

ExistsInWAL(r, seqNo) ==
    /\ rWalStaging[r] /= None
    /\ \E i \in DOMAIN CachedManifest(r).fragments : 
        CachedManifest(r).fragments[i].seqNo = seqNo

\* Read a fragment, returns the fragment, or NotFound or None
WalReadFragment(r, seqNo) ==
    CASE /\ ExistsInWAL(r, seqNo) 
         /\ seqNo \in DOMAIN fragments -> fragments[seqNo]
      [] /\ ExistsInWAL(r, seqNo) 
         /\ seqNo \notin DOMAIN fragments -> NotFound
      [] OTHER -> None

EndCompaction(r) ==
    /\ rCompState' = [rCompState EXCEPT ![r] = IDLE]
    /\ rCompCheckpoint' = [rCompCheckpoint EXCEPT ![r] = None]
    /\ rCompCursor' = [rCompCursor EXCEPT ![r] = None]

\* ****************************************************
\* WAL APPEND ACTIONS
\* ****************************************************

(* ---------------------------------------------------------
    ACTION: WalRefreshManifest

    DESC TODO
-----------------------------------------------------------*)
WalRefreshManifest(r) ==
    /\ rWalState[r] \in {IDLE, REFRESH}
    /\ ~IsManifestLocked(r)
    /\ rWalStaging' = [rWalStaging EXCEPT ![r] = 
                            SetStagingFromManifest(r, manifest)]
    /\ rWalState' = [rWalState EXCEPT ![r] = RECOVER]
    /\ UNCHANGED <<storeVars, auxVars, repGcVars, repCompVars,
                   rWalPendingValues>>

(* ---------------------------------------------------------
    ACTION: WalRecover

    DESC TODO
-----------------------------------------------------------*)

DoingWrite(r) == rWalPendingValues[r] /= {}

PostRefreshState(r) ==
    IF DoingWrite(r) THEN UPLOAD_FRAGMMENT
    ELSE READY

WalRecover(r) ==
    /\ rWalState[r] = RECOVER
    /\ \/ /\ rWalStaging[r].nextSeqNo \in DOMAIN fragments 
          /\ LET frag == fragments[rWalStaging[r].nextSeqNo]IN 
              /\ rWalState' = [rWalState EXCEPT ![r] = COMMIT_RECOVERED]
              /\ rWalStaging' = [rWalStaging EXCEPT ![r].fragment = frag]
       \/ /\ rWalStaging[r].nextSeqNo \notin DOMAIN fragments 
          /\ rWalState' = [rWalState EXCEPT ![r] = PostRefreshState(r)]
          /\ UNCHANGED rWalStaging
    /\ UNCHANGED <<storeVars, auxVars, repGcVars, repCompVars, 
                   rWalPendingValues>>

(* ---------------------------------------------------------
    ACTION: WalCommitRecoveredFragment

    DESC TODO
-----------------------------------------------------------*)

WalCommitRecoveredFragment(r) ==
    /\ rWalState[r] = COMMIT_RECOVERED
    /\ ~IsManifestLocked(r)
    /\ \/ /\ CachedManifest(r).version = manifest.version
          /\ CommitFragment(r)
          /\ rWalState' = [rWalState EXCEPT ![r] = PostRefreshState(r)]
       \/ /\ CachedManifest(r).version /= manifest.version
          /\ rWalState' = [rWalState EXCEPT ![r] = REFRESH]
          /\ NoCommit
    /\ UNCHANGED <<fragments, checkpoint, compCursor, gcPlanFile, 
                   auxUsedValues, repGcVars, repCompVars, rWalPendingValues>>

(* ---------------------------------------------------------
    ACTION: WalAcceptWrites

    DESC TODO
-----------------------------------------------------------*)

WalAcceptWrites(r, values) ==
    /\ rWalState[r] = READY
    /\ Cardinality(values) > 0
    /\ \A v \in values : v \notin auxUsedValues
    /\ rWalPendingValues' = [rWalPendingValues EXCEPT ![r] = values]
    /\ rWalState' = [rWalState EXCEPT ![r] = UPLOAD_FRAGMMENT]
    /\ auxUsedValues' = auxUsedValues \union values
    /\ UNCHANGED <<storeVars, auxCommitted, repGcVars, repCompVars, 
                   rWalStaging>>

(* ---------------------------------------------------------
    ACTION: WalUploadFragment

    DESC TODO
-----------------------------------------------------------*)

WalUploadFragment(r) ==
    /\ rWalState[r] = UPLOAD_FRAGMMENT
    /\ LET seq     == SetToSeq(rWalPendingValues[r])
           entries == [i \in DOMAIN seq |-> 
                            [pos  |-> rWalStaging[r].nextPos + i - 1,
                             data |-> seq[i]]]
           frag    == [seqNo   |-> rWalStaging[r].nextSeqNo,
                       entries |-> entries]
        IN
            \/ /\ frag.seqNo \in DOMAIN fragments
               /\ rWalState' = [rWalState EXCEPT ![r] = REFRESH]
               /\ UNCHANGED <<fragments, rWalStaging>>
            \/ /\ frag.seqNo \notin DOMAIN fragments 
               /\ fragments' = fragments @@ (frag.seqNo :> frag)
               /\ rWalStaging' = [rWalStaging EXCEPT ![r].fragment = frag]
               /\ rWalState' = [rWalState EXCEPT ![r] = COMMIT_FRAGMENT]
    /\ UNCHANGED <<manifest, checkpoint, compCursor, gcPlanFile, auxVars, 
                   repGcVars, repCompVars, rWalPendingValues>>

(* ---------------------------------------------------------
    ACTION: WalCommitFragment

    DESC TODO
-----------------------------------------------------------*)

WalCommitFragment(r) ==
    /\ rWalState[r] = COMMIT_FRAGMENT
    /\ ~IsManifestLocked(r)
    /\ \/ /\ CachedManifest(r).version = manifest.version
          /\ CommitFragment(r)
          /\ rWalState' = [rWalState EXCEPT ![r] = READY]
          /\ rWalPendingValues' = [rWalPendingValues EXCEPT ![r] = {}]
       \/ /\ CachedManifest(r).version /= manifest.version
          /\ rWalState' = [rWalState EXCEPT ![r] = PREEMPTED]
          /\ NoCommit
          /\ UNCHANGED <<rWalPendingValues>>
    /\ UNCHANGED <<fragments, checkpoint, compCursor, gcPlanFile,
                   auxUsedValues, repGcVars, repCompVars>>

\* ****************************************************
\* WAL GC ACTIONS
\* ****************************************************

(* ---------------------------------------------------------
    ACTION: GcPhase1ReadCursor

    DESC TODO
-----------------------------------------------------------*)

\* This is not the protocol, just some state space reduction
\* to avoid triggering GC that will collect nothing
CanAdvanceGcBoundary(r) ==
    \* There are fragments at all
    /\ rWalStaging[r] /= None
    /\ CachedManifest(r).fragments /= <<>>
    \* The compaction cursor covers the WAL
    /\ compCursor.pos > ManifestPosFloor(r)
    
GcPhase1ReadCursor(r) ==
    /\ rGcState[r] = IDLE
    /\ CanAdvanceGcBoundary(r)
    /\ rGcCompCursor' = [rGcCompCursor EXCEPT ![r] = compCursor]
    /\ rGcState' = [rGcState EXCEPT ![r] = GC_P1_READ_GC_FILE]
    /\ UNCHANGED <<storeVars, auxVars, repWalVars, repCompVars,
                   rGcPlanFile>>

(* ---------------------------------------------------------
    ACTION: GcPhase1ReadGcFile

    DESC TODO
-----------------------------------------------------------*)

GcPhase1ReadGcFile(r) ==
    /\ rGcState[r] = GC_P1_READ_GC_FILE
    /\ rGcPlanFile' = [rGcPlanFile EXCEPT ![r] = gcPlanFile]
    /\ rGcState' = [rGcState EXCEPT ![r] = GC_P1_COMPUTE_PLAN]
    /\ UNCHANGED <<storeVars, auxVars, repWalVars, repCompVars,
                   rGcCompCursor>>

(* ---------------------------------------------------------
    ACTION: GcPhase1ComputePlan

    DESC TODO
-----------------------------------------------------------*)

GcFileEmpty(r) == rGcPlanFile[r].seqNoLimit = 0
GcFileStillApplicable(r) == 
    /\ rGcPlanFile[r].seqNoLimit >= ManifestSeqNoFloor(r) + 1
    /\ rGcPlanFile[r].seqNoLimit <= ManifestSeqNoCeiling(r) + 1
GcFileNotApplicable(r) ==
    ~GcFileStillApplicable(r)

NothingToCollect(r) ==
    LET firstToKeep == rGcCompCursor[r].pos + 1
        frag == CachedManifest(r).fragments
    IN ~\E i \in DOMAIN frag : frag[i].limit <= firstToKeep

ComputeGcLimit(r, pos) ==
    LET firstToKeep == rGcCompCursor[r].pos + 1
        frag == CachedManifest(r).fragments
        max  == CHOOSE i \in DOMAIN frag :
                    /\ frag[i].limit <= firstToKeep
                    /\ ~\E j \in DOMAIN frag :
                        /\ frag[j].limit <= firstToKeep
                        /\ j > i
    IN frag[max].seqNo + 1

GcFileMatch(r) ==
    \/ gcPlanFile = None 
    \/ /\ rGcPlanFile[r] /= None
       /\ rGcPlanFile[r].version = gcPlanFile.version

SaveComputedPlan(r) ==
    LET gcLimit   == ComputeGcLimit(r, rGcCompCursor[r]) 
        newGcFile == [seqNoLimit |-> gcLimit, 
                      version    |-> gcPlanFile.version + 1]
    IN
        \/ /\ GcFileMatch(r)
           /\ gcPlanFile' = newGcFile
           /\ rGcPlanFile' = [rGcPlanFile EXCEPT ![r] = newGcFile]
           /\ rWalStaging' = [rWalStaging EXCEPT ![r].locked = TRUE]
           /\ rGcState' = [rGcState EXCEPT ![r] = GC_P2_READ_GC_FILE]
        \/ /\ ~GcFileMatch(r)
           /\ rGcState' = [rGcState EXCEPT ![r] = GC_P1_READ_GC_FILE]
           /\ UNCHANGED <<gcPlanFile, rWalStaging, rGcPlanFile>>  

ReusePlan(r) ==
    /\ rWalStaging' = [rWalStaging EXCEPT ![r].locked = TRUE]
    /\ rGcState' = [rGcState EXCEPT ![r] = GC_P2_READ_GC_FILE]
    /\ UNCHANGED <<gcPlanFile, rGcPlanFile>>  

ResetPlan(r) ==
    /\ IF rGcPlanFile[r].version = gcPlanFile.version
       THEN gcPlanFile' = [seqNoLimit |-> 0, 
                           version    |-> gcPlanFile.version + 1]
       ELSE UNCHANGED gcPlanFile    
    /\ rGcState' = [rGcState EXCEPT ![r] = GC_P1_READ_GC_FILE]
    /\ UNCHANGED <<rWalStaging, rGcPlanFile>>

AbortGc(r) ==
    /\ rGcState' = [rGcState EXCEPT ![r] = IDLE]
    /\ UNCHANGED <<gcPlanFile, rWalStaging, rGcPlanFile>>    

GcPhase1ComputePlan(r) ==
    /\ rGcState[r] = GC_P1_COMPUTE_PLAN
    /\ CASE NothingToCollect(r) ->
                AbortGc(r)
         [] GcFileEmpty(r) ->
                SaveComputedPlan(r)
         [] GcFileStillApplicable(r) -> 
                ReusePlan(r)
         [] GcFileNotApplicable(r) -> 
                ResetPlan(r)
    /\ UNCHANGED <<manifest, fragments, checkpoint, compCursor, rGcCompCursor,
                   auxVars, rWalState, rWalPendingValues, repCompVars>>


(* ---------------------------------------------------------
    ACTION: GcPhase2ReadGcFile

    DESC TODO
-----------------------------------------------------------*)

GcPhase2ReadGcFile(r) ==
    /\ rGcState[r] = GC_P2_READ_GC_FILE
    /\ rGcPlanFile' = [rGcPlanFile EXCEPT ![r] = gcPlanFile]
    /\ rWalStaging' = [rWalStaging EXCEPT ![r].gcLimit = gcPlanFile.seqNoLimit]
    /\ rGcState' = [rGcState EXCEPT ![r] = GC_P2_CAS_MANIFEST]
    /\ UNCHANGED <<storeVars, auxVars, rWalState, rWalPendingValues, 
                   repCompVars, rGcCompCursor>>

(* ---------------------------------------------------------
    ACTION: GcPhase2CasManifest

    DESC TODO
-----------------------------------------------------------*)

TrimmedFragments(r) ==
    LET limit == rWalStaging[r].gcLimit
        frags == CachedManifest(r).fragments
        i == CHOOSE i \in DOMAIN frags :
                frags[i].seqNo = limit - 1
    IN IF i = Len(frags) THEN <<>>
       ELSE SubSeq(frags, i+1, Len(frags))

GcPhase2CasManifest(r) ==
    /\ rGcState[r] = GC_P2_CAS_MANIFEST
    /\ LET trimmed == TrimmedFragments(r)
           m       == CachedManifest(r)
           initialPos == IF trimmed = <<>> THEN NextPos(m) ELSE m.initialPos
           initialSeqNo == IF trimmed = <<>> THEN NextSeqNo(m) ELSE m.initialSeqNo
           newManifest == [m EXCEPT !.fragments = trimmed,
                                    !.initialPos = initialPos,
                                    !.initialSeqNo = initialSeqNo,
                                    !.version = @ + 1]
       IN CASE ~GcFileStillApplicable(r) ->
                /\ rGcState' = [rGcState EXCEPT ![r] = IDLE]
                /\ rWalStaging' = [rWalStaging EXCEPT ![r].locked = FALSE]
                /\ UNCHANGED manifest
            [] m.version = manifest.version ->
                /\ manifest' = newManifest
                /\ rWalStaging' = [rWalStaging EXCEPT ![r].manifest = newManifest,
                                                      ![r].locked = FALSE]
                /\ rGcState' = [rGcState EXCEPT ![r] = GC_P3_READ_GC_FILE] 
            [] m.version /= manifest.version ->
                /\ rWalStaging' = [rWalStaging EXCEPT ![r].locked = FALSE]
                /\ rGcState' = [rGcState EXCEPT ![r] = PREEMPTED]
                /\ UNCHANGED <<manifest>>
    /\ UNCHANGED <<fragments, checkpoint, compCursor, gcPlanFile, auxVars, 
                   repCompVars, rWalState, rWalPendingValues, rGcPlanFile,
                   rGcCompCursor>>

(* ---------------------------------------------------------
    ACTION: GcPhase3ReadGcFile

    DESC TODO
-----------------------------------------------------------*)

GcPhase3ReadGcFile(r) ==
    /\ rGcState[r] = GC_P3_READ_GC_FILE
    /\ rGcPlanFile' = [rGcPlanFile EXCEPT ![r] = gcPlanFile]
    /\ rWalStaging' = [rWalStaging EXCEPT ![r].gcLimit = gcPlanFile.seqNoLimit]
    /\ rGcState' = [rGcState EXCEPT ![r] = GC_P3_DELETE]
    /\ UNCHANGED <<storeVars, auxVars, rWalState, rWalPendingValues, 
                   repCompVars, rGcCompCursor>>

(* ---------------------------------------------------------
    ACTION: GcPhase3Delete

    DESC TODO
-----------------------------------------------------------*)

GcPhase3Delete(r) ==
    /\ rGcState[r] = GC_P3_DELETE
    /\ \E seqNo \in DOMAIN fragments :
        /\ seqNo < rWalStaging[r].gcLimit
        /\ fragments' = [sn \in (DOMAIN fragments \ {seqNo}) |->
                              fragments[sn]]
    /\ UNCHANGED <<manifest, checkpoint, compCursor, gcPlanFile,
                  auxVars, repCompVars, repWalVars, repGcVars>>

(* ---------------------------------------------------------
    ACTION: GcPhase3Complete

    DESC TODO
-----------------------------------------------------------*)

GcPhase3Complete(r) ==
    /\ rGcState[r] = GC_P3_DELETE
    /\ ~\E seqNo \in DOMAIN fragments : seqNo < rWalStaging[r].gcLimit
    /\ IF GcFileMatch(r) 
       THEN /\ gcPlanFile' = [seqNoLimit |-> 0, 
                              version    |-> gcPlanFile.version + 1]
            /\ rGcPlanFile' = [rGcPlanFile EXCEPT ![r] = None]
            /\ rGcCompCursor' = [rGcCompCursor EXCEPT ![r] = None]
       ELSE UNCHANGED <<gcPlanFile, rGcPlanFile, rGcCompCursor>>
    /\ rGcState' = [rGcState EXCEPT ![r] = IDLE] 
    /\ UNCHANGED <<manifest, fragments, checkpoint, compCursor, 
                  auxVars, repCompVars, repWalVars>>                  

\* ****************************************************
\* COMPACTION ACTIONS
\* ****************************************************

(* ---------------------------------------------------------
    ACTION: CompactorStart

    DESC TODO
-----------------------------------------------------------*)

\* Trigger when no compaction running and WAL has
\* started. Also to reduce state space, only trigger
\* when the WAL has advanced past the current checkpoint
TriggerCompaction(r) ==
    /\ rCompState[r] = IDLE
    /\ rWalStaging[r] /= None
    /\ NextSeqNo(CachedManifest(r))-1  > checkpoint.seqNo

CompactorStart(r) ==
    /\ TriggerCompaction(r)
    /\ rCompCheckpoint' = [rCompCheckpoint EXCEPT ![r] = checkpoint]
    /\ rCompState' = [rCompState EXCEPT ![r] = REPLAY_WAL]
    /\ UNCHANGED <<storeVars, auxVars, repWalVars, repGcVars, rCompCursor>>
    
(* ---------------------------------------------------------
    ACTION: CompactorReplayWAL

    DESC TODO
-----------------------------------------------------------*)

CompactorReplayWAL(r) ==
    /\ rCompState[r] = REPLAY_WAL
    /\ LET nextSeqNo == rCompCheckpoint[r].seqNo + 1
           frag      == WalReadFragment(r, nextSeqNo)
       IN
          CASE frag = NotFound ->
                EndCompaction(r)
            [] frag = None ->
                /\ rCompState' = [rCompState EXCEPT ![r] = COMMIT_CHECKPOINT]
                /\ UNCHANGED <<rCompCheckpoint, rCompCursor>>
            [] OTHER ->
                /\ rCompCheckpoint' = [rCompCheckpoint EXCEPT ![r].snapshot = @ \o frag.entries,
                                                                ![r].seqNo = frag.seqNo]
                /\ UNCHANGED <<rCompState, rCompCursor>>
    /\ UNCHANGED <<storeVars, auxVars, repWalVars, repGcVars>>

(* ---------------------------------------------------------
    ACTION: CompactorCommitCheckpoint

    DESC TODO
-----------------------------------------------------------*)

CompactorCommitCheckpoint(r) ==
    /\ rCompState[r] = COMMIT_CHECKPOINT
    /\ \/ /\ rCompCheckpoint[r].version = checkpoint.version
          /\ checkpoint' = [rCompCheckpoint[r] EXCEPT !.version = @ + 1]
          /\ rCompState' = [rCompState EXCEPT ![r] = READ_CURSOR]
          /\ UNCHANGED <<rCompCheckpoint, rCompCursor>>
       \/ /\ rCompCheckpoint[r].version /= checkpoint.version
          /\ EndCompaction(r)
          /\ UNCHANGED checkpoint
    /\ UNCHANGED <<manifest, fragments, gcPlanFile, compCursor,
                   auxVars, repWalVars, repGcVars>>

(* ---------------------------------------------------------
    ACTION: CompactorReadCursor

    DESC TODO
-----------------------------------------------------------*)

CompactorReadCursor(r) ==
    /\ rCompState[r] = READ_CURSOR
    /\ \/ /\ compCursor.pos >= LocalCheckpointPos(r)
          /\ EndCompaction(r)
       \/ /\ compCursor.pos < LocalCheckpointPos(r)
          /\ rCompCursor' = [rCompCursor EXCEPT ![r] = compCursor]
          /\ rCompState' = [rCompState EXCEPT ![r] = COMMIT_CURSOR]
          /\ UNCHANGED <<rCompCheckpoint>>
    /\ UNCHANGED <<storeVars, auxVars, repWalVars, repGcVars>>

(* ---------------------------------------------------------
    ACTION: CompactorCommitCursor

    DESC TODO
-----------------------------------------------------------*)

CompactorCommitCursor(r) ==
    /\ rCompState[r] = COMMIT_CURSOR
    /\ LET newCursor == [rCompCursor[r] EXCEPT !.pos = LocalCheckpointPos(r),
                                               !.version = @ + 1]
       IN 
            /\ IF rCompCursor[r].version = compCursor.version
               THEN compCursor' = newCursor
               ELSE UNCHANGED compCursor
            /\ EndCompaction(r)
    /\ UNCHANGED <<manifest, fragments, checkpoint, gcPlanFile, 
                   auxVars, repWalVars, repGcVars>>

\* ****************************************************
\* DATA MODEL
\* ****************************************************

LogEntryType == [pos: Nat, data: Values]

FragmentType ==
    [seqNo: Nat,
     entries: Seq(LogEntryType)]

FragmentRefType == 
    [seqNo: Nat, 
     start: Nat, 
     limit: Nat]

ManifestType ==
    [fragments: Seq(FragmentRefType),
     initialSeqNo: Nat,
     initialPos: Nat,
     version: Nat]
        \union {None}

StagingType ==
    [manifest: ManifestType,
     fragment: FragmentType \union {None}, \* should be a FragRef but TLA+ is simpler this way
     nextPos: Nat,
     nextSeqNo: Nat,
     gcLimit: Nat,
     locked: BOOLEAN]
        \union {None}

CheckpointType == [snapshot: Seq(LogEntryType),
                   seqNo: Nat,
                   version: Nat] \union {None}

GcPlanFileType == [seqNoLimit: Nat, version: Nat] \union {None}
CompactionCursorType == [pos: Nat, version: Nat] \union {None}

\* role states
WalStates    == {IDLE, REFRESH, RECOVER, COMMIT_RECOVERED, READY, UPLOAD_FRAGMMENT, 
                 COMMIT_FRAGMENT, ABORT_WRITE, ILLEGAL_STATE, PREEMPTED}
GcStates     == {IDLE, PREEMPTED,
                 GC_P1_READ_GC_FILE, GC_P1_COMPUTE_PLAN, 
                 GC_P2_READ_GC_FILE, GC_P2_CAS_MANIFEST, 
                 GC_P3_READ_GC_FILE, GC_P3_DELETE}
CompactionStates == {IDLE, REPLAY_WAL, COMMIT_CHECKPOINT, READ_CURSOR, COMMIT_CURSOR}

TypeOK ==
    /\ manifest \in ManifestType
    /\ \A id \in DOMAIN fragments :
        fragments[id] \in FragmentType
    /\ checkpoint \in CheckpointType
    /\ compCursor \in CompactionCursorType
    /\ gcPlanFile \in GcPlanFileType
    /\ rWalState \in [Replicas -> WalStates]
    /\ rWalStaging \in [Replicas -> StagingType]
    /\ rWalPendingValues \in [Replicas -> SUBSET Values]
    /\ rGcState \in [Replicas -> GcStates]
    /\ rGcPlanFile \in [Replicas -> GcPlanFileType]
    /\ rGcCompCursor \in [Replicas -> CompactionCursorType]
    /\ rCompState \in [Replicas -> CompactionStates]
    /\ rCompCheckpoint \in [Replicas -> CheckpointType]
    /\ rCompCursor \in [Replicas -> CompactionCursorType]
    /\ auxUsedValues \in SUBSET Values
    /\ auxCommitted \in Seq(LogEntryType)

\* ****************************************************
\* PROPERTIES
\* ****************************************************

\* INV: ValidFragments
\* Both fragments and fragment refs are contiguous (no
\* gaps, no overlap) and fragment refs are consistent with fragments
ValidFragments ==
    \* Fragment entries are contiguous
    /\ ~\E id1, id2 \in DOMAIN fragments :
        /\ id1 + 1 = id2
        /\ MaxPos(fragments[id1].entries) + 1 /= MinPos(fragments[id2].entries)
        /\ fragments[id1].seqNo + 1 = fragments[id2].seqNo
    \* Fragment refs point to written fragment addresses and their bounds match
    /\ \A i \in DOMAIN manifest.fragments :
        LET ref == manifest.fragments[i] IN
            /\ ref.seqNo \in DOMAIN fragments
            /\ ref.start = MinPos(fragments[ref.seqNo].entries)
            /\ ref.limit -1 = MaxPos(fragments[ref.seqNo].entries)
    \* Fragment refs are contiguous
    /\ ~\E i, j \in DOMAIN manifest.fragments :
        /\ i + 1 = j
        /\ manifest.fragments[i].limit /= manifest.fragments[j].start
        /\ manifest.fragments[i].seqNo + 1 = manifest.fragments[j].seqNo
        
\* INV: ValidReplicas
\* There must be at least one functional wal writer
\* and no wal writer entered an illegal state
ValidReplicas ==
    /\ \E r \in Replicas : rWalState[r] /= PREEMPTED 
    /\ ~\E r \in Replicas : rWalState[r] = ILLEGAL_STATE

\* INV: ConsistentCheckpoint
\* If the checkpoint is stale, it matches a prefix of write history.
\* If the checkpoint is current, it perfectly matches the write history.
SeqPrefixOf(s1, s2) ==
    /\ Len(s1) <= Len(s2)
    /\ \A pos \in DOMAIN s1 :
            s1[pos] = s2[pos]

ConsistentCheckpoint == 
    IF checkpoint.seqNo = NextSeqNo(manifest) - 1
    THEN checkpoint.snapshot = auxCommitted
    ELSE SeqPrefixOf(checkpoint.snapshot, auxCommitted)

\* INV: ManifestRepresentsCommittedLog
\* Compare the checkpoint and every referenced fragment with the history
\* slice for its position range, including fragments covered by the checkpoint.
ManifestRepresentsCommittedLog ==
    LET snap == checkpoint.snapshot
        lastPos == IF snap = <<>> THEN 0 ELSE Last(snap).pos
    IN
        /\ lastPos <= Len(auxCommitted)
        /\ snap = SubSeq(auxCommitted, 1, lastPos)
        /\ \A i \in DOMAIN manifest.fragments :
            LET ref == manifest.fragments[i]
            IN /\ ref.seqNo \in DOMAIN fragments
               /\ ref.start >= 1
               /\ ref.limit <= Len(auxCommitted) + 1
               /\ fragments[ref.seqNo].entries =
                       SubSeq(auxCommitted, ref.start, ref.limit - 1)


AllValuesAttempted ==
    <>[](auxUsedValues = Values)

OpsEventuallyComplete ==
    \A r \in Replicas :
        /\ rWalState[r] /= IDLE ~> rWalState[r] \in {READY, PREEMPTED}
        /\ rGcState[r] /= IDLE ~> rGcState[r] \in {IDLE, PREEMPTED}
        /\ rCompState[r] /= IDLE ~> rCompState[r] = IDLE

\* ****************************************************
\* Init, Next and Spec
\* ****************************************************

Init ==
    /\ manifest = [fragments    |-> <<>>, 
                   initialSeqNo |-> 1,
                   initialPos   |-> 1, 
                   version      |-> 0]
    /\ fragments = <<>>
    /\ checkpoint = [seqNo |-> 0, snapshot |-> <<>>, version |-> 1]
    /\ compCursor = [pos |-> 0, version |-> 1]
    /\ gcPlanFile = [seqNoLimit |-> 0, version |-> 1] 
    /\ rWalState = [r \in Replicas |-> IDLE]
    /\ rWalStaging = [r \in Replicas |-> None]
    /\ rWalPendingValues = [r \in Replicas |-> {}]
    /\ rGcState = [r \in Replicas |-> IDLE]
    /\ rGcPlanFile = [r \in Replicas |-> None]
    /\ rGcCompCursor = [r \in Replicas |-> None]
    /\ rCompState = [r \in Replicas |-> IDLE]
    /\ rCompCheckpoint = [r \in Replicas |-> None]
    /\ rCompCursor = [r \in Replicas |-> None]
    /\ auxUsedValues = {}
    /\ auxCommitted = <<>>

Next ==
    \E r \in Replicas :
        \/ WalRefreshManifest(r)
        \* WAL writer appends
        \/ WalRecover(r)
        \/ WalCommitRecoveredFragment(r)
        \/ \E values \in SUBSET Values : WalAcceptWrites(r, values)
        \/ WalUploadFragment(r)
        \/ WalCommitFragment(r)
        \* \/ WalAbortWrite(r)
        \* WAL writer GC
        \/ GcPhase1ReadCursor(r)
        \/ GcPhase1ReadGcFile(r)
        \/ GcPhase1ComputePlan(r)
        \/ GcPhase2ReadGcFile(r)
        \/ GcPhase2CasManifest(r)
        \/ GcPhase3ReadGcFile(r)
        \/ GcPhase3Delete(r)
        \/ GcPhase3Complete(r)
        \* App apply
        \/ CompactorStart(r)
        \/ CompactorReplayWAL(r)
        \/ CompactorCommitCheckpoint(r)
        \/ CompactorReadCursor(r)
        \/ CompactorCommitCursor(r)

Fairness ==
    \A r \in Replicas :
        /\ WF_vars(WalRefreshManifest(r))
        /\ WF_vars(WalRecover(r))
        /\ WF_vars(WalCommitRecoveredFragment(r))
        /\ \A values \in SUBSET Values : WF_vars(WalAcceptWrites(r, values))
        /\ WF_vars(WalUploadFragment(r))
        /\ WF_vars(WalCommitFragment(r))
        \* /\ WF_vars(GcPhase1ReadCursor(r))
        /\ WF_vars(GcPhase1ReadGcFile(r))
        /\ WF_vars(GcPhase1ComputePlan(r))
        /\ WF_vars(GcPhase2ReadGcFile(r))
        /\ WF_vars(GcPhase2CasManifest(r))
        /\ WF_vars(GcPhase3ReadGcFile(r))
        /\ WF_vars(GcPhase3Delete(r))
        /\ WF_vars(GcPhase3Complete(r))
        \* /\ WF_vars(CompactorStart(r))
        /\ WF_vars(CompactorReplayWAL(r))
        /\ WF_vars(CompactorCommitCheckpoint(r))
        /\ WF_vars(CompactorReadCursor(r))
        /\ WF_vars(CompactorCommitCursor(r)        )

Spec == Init /\ [][Next]_vars
LivenessSpec == Init /\ [][Next]_vars /\ Fairness

========================================================================
