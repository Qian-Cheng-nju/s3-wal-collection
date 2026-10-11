----------------------------- MODULE Wal3Common -----------------------------

EXTENDS Naturals, Integers, FiniteSets, FiniteSetsExt, Sequences,
        SequencesExt, TLC

(*
    Contains:
        * constants
        * variables
        * shared helpers
        * data model and TypeOK
        * NO actions
*)

CONSTANTS Replicas, \* The set of replica processes
          Values   \* The set of values to append

\* Replica states
CONSTANTS IDLE, RECOVER, COMMIT_RECOVERED, REFRESH, READY,
          UPLOAD_FRAGMENT, COMMIT_FRAGMENT,
          ILLEGAL_STATE, ABORT_WRITE, PREEMPTED,
          REPLAY_WAL, COMMIT_CHECKPOINT, READ_CURSOR, COMMIT_CURSOR,
          GC_P1_READ_GC_FILE, GC_P1_COMPUTE_PLAN,
          GC_P2_READ_GC_FILE, GC_P2_CAS_MANIFEST,
          GC_P3_READ_GC_FILE, GC_P3_READ_MANIFEST, GC_P3_DELETE,
          ABORTED

CONSTANTS None, NotFound

\* Durable state on S3
VARIABLES manifest,      \* CAS protected leader state manifest file
          fragments,     \* Id -> Log entry file
          checkpoint,    \* very abstract published state storage (indexes etc)
          gcPlanFile,    \* GARBAGE file
          compCursor     \* Compaction cursor

\* Shared replica metadata and coordination
\* All three roles read the cached manifest; writer and GC update it.
VARIABLES rManifest,        \* Replica -> cached manifest, or None before refresh
          rManifestLocked   \* Replica -> local serialization of manifest updates

\* WAL writer (appends) state
VARIABLES rWriterState,         \* Replica -> current writer state
          rWriterPendingValues, \* Replica -> values pending commit
          rWriterFragment,      \* Replica -> uploaded or recovered fragment to commit
          rWriterNextPos,       \* Replica -> next append position
          rWriterNextSeqNo      \* Replica -> next fragment sequence number

\* WAL GC task state
VARIABLES rGcState,         \* Replica -> current GC state
          rGcCachedPlan,    \* Replica -> most recently read or written GC plan
          rGcPinnedPlan,    \* Replica -> GC plan retained from phase 1
          rGcTrimLimit,     \* Replica -> exclusive seqNo limit for phase 2 trimming
          rGcCompCursor     \* Replica -> cached compaction cursor

\* Compaction state
VARIABLES rCompState,       \* Replica -> current state
          rCompCheckpoint,  \* Replica -> working checkpoint extended during replay
          rCompCursor       \* Replica -> cached compaction cursor

VARIABLES auxUsedValues,
          auxCommitted \* Successful write history

storeVars == <<manifest, fragments, checkpoint, compCursor,
               gcPlanFile>>
repSharedVars == <<rManifest, rManifestLocked>>
repWriterVars == <<rWriterState, rWriterPendingValues, rWriterFragment,
                   rWriterNextPos, rWriterNextSeqNo>>
repGcVars == <<rGcState, rGcCachedPlan, rGcPinnedPlan, rGcTrimLimit,
               rGcCompCursor>>
repCompVars == <<rCompState, rCompCheckpoint, rCompCursor>>
replicaVars == <<repSharedVars, repWriterVars, repGcVars, repCompVars>>
auxVars == <<auxUsedValues, auxCommitted>>
vars == <<storeVars, replicaVars, auxVars>>

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

\* Note:
\* initial* fields act as initial values but also advance
\* when the fragRef list is emptied by GC
ManifestType ==
    [fragRefs: Seq(FragmentRefType),
     initialSeqNo: Nat,
     initialPos: Nat,
     version: Nat]
        \union {None}

\* The checkpoint serves as an abstract representation
\* of published Chroma state (like indexes etc)
CheckpointType == [snapshot: Seq(LogEntryType),
                   seqNo: Nat,
                   version: Nat] \union {None}

\* A simplified GARBAGE file, just the GC log pos boundary
GcPlanType == [seqNoLimit: Nat, version: Nat] \union {None}
\* The inclusive current position that compaction has reached
CompactionCursorType == [pos: Nat, version: Nat] \union {None}

\* role states
WriterStates == {IDLE, REFRESH, RECOVER, COMMIT_RECOVERED, READY,
                 UPLOAD_FRAGMENT, COMMIT_FRAGMENT, ABORT_WRITE,
                 ILLEGAL_STATE, PREEMPTED}
GcStates == {IDLE, ABORTED, PREEMPTED,
             GC_P1_READ_GC_FILE, GC_P1_COMPUTE_PLAN,
             GC_P2_READ_GC_FILE, GC_P2_CAS_MANIFEST,
             GC_P3_READ_GC_FILE, GC_P3_READ_MANIFEST, GC_P3_DELETE}
CompactionStates == {IDLE, REPLAY_WAL, COMMIT_CHECKPOINT, READ_CURSOR, COMMIT_CURSOR}

TypeOK ==
    /\ manifest \in ManifestType
    /\ \A id \in DOMAIN fragments :
        fragments[id] \in FragmentType
    /\ checkpoint \in CheckpointType
    /\ compCursor \in CompactionCursorType
    /\ gcPlanFile \in GcPlanType
    /\ rManifest \in [Replicas -> ManifestType]
    /\ rManifestLocked \in [Replicas -> BOOLEAN]
    /\ rWriterState \in [Replicas -> WriterStates]
    /\ rWriterPendingValues \in [Replicas -> SUBSET Values]
    /\ rWriterFragment \in [Replicas -> FragmentType \union {None}]
    /\ rWriterNextPos \in [Replicas -> Nat]
    /\ rWriterNextSeqNo \in [Replicas -> Nat]
    /\ rGcState \in [Replicas -> GcStates]
    /\ rGcCachedPlan \in [Replicas -> GcPlanType]
    /\ rGcPinnedPlan \in [Replicas -> GcPlanType]
    /\ rGcTrimLimit \in [Replicas -> Nat]
    /\ rGcCompCursor \in [Replicas -> CompactionCursorType]
    /\ rCompState \in [Replicas -> CompactionStates]
    /\ rCompCheckpoint \in [Replicas -> CheckpointType]
    /\ rCompCursor \in [Replicas -> CompactionCursorType]
    /\ auxUsedValues \in SUBSET Values
    /\ auxCommitted \in Seq(LogEntryType)

\* ****************************************************
\* COMMON Init
\* ****************************************************

CommonInit ==
    /\ rManifest = [r \in Replicas |-> None]
    /\ rManifestLocked = [r \in Replicas |-> FALSE]

\* ****************************************************
\* COMMON HELPERS
\* ****************************************************

NextPos(m) ==
    IF m.fragRefs = <<>> THEN m.initialPos
    ELSE Last(m.fragRefs).limit

NextSeqNo(m) ==
    IF m.fragRefs = <<>> THEN m.initialSeqNo
    ELSE Last(m.fragRefs).seqNo + 1

FloorSeqNo(m) ==
    IF m.fragRefs = <<>>
    THEN m.initialSeqNo
    ELSE Head(m.fragRefs).seqNo

CachedSeqNoFloor(r)   == FloorSeqNo(rManifest[r])
CachedSeqNoCeiling(r) == NextSeqNo(rManifest[r]) - 1

EmptyManifest(r) ==
    \/ rManifest[r] = None
    \/ /\ rManifest[r] /= None
       /\ rManifest[r].fragRefs = <<>>

CachedFloorLogPos(r) ==
    IF EmptyManifest(r) THEN 0
    ELSE Head(rManifest[r].fragRefs).start

CachedCeilingLogPos(r) ==
    IF EmptyManifest(r) THEN 0
    ELSE Last(rManifest[r].fragRefs).limit - 1

\* min/max pos in fragment file
MinLogPos(frag) == Head(frag.entries).pos
MaxLogPos(frag) == Last(frag.entries).pos

\* Build a fragment ref from a fragment
FragRef(frag) ==
    [seqNo |-> frag.seqNo,
     start |-> MinLogPos(frag),
     limit |-> MaxLogPos(frag) + 1]

PlanApplied(m, plan) == FloorSeqNo(m) >= plan.seqNoLimit

IsManifestLocked(r) == rManifestLocked[r]

PreemptWriterAndGc(r) ==
    /\ rWriterState' = [rWriterState EXCEPT ![r] = PREEMPTED]
    /\ rGcState' = [rGcState EXCEPT ![r] = PREEMPTED]

\* WAL reads --------------------------------------------

FragInManifest(r, seqNo) ==
    \E i \in DOMAIN rManifest[r].fragRefs :
        rManifest[r].fragRefs[i].seqNo = seqNo

FragWritten(seqNo) ==
    seqNo \in DOMAIN fragments

WalRead(r, seqNo) ==
    IF FragInManifest(r, seqNo)
    THEN IF FragWritten(seqNo)
         THEN fragments[seqNo]
         ELSE NotFound
    ELSE None

=============================================================================
