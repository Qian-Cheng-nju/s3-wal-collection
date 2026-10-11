----------------------------- MODULE Wal3Compactor -----------------------------

EXTENDS Wal3Common

(* 
    Compaction protocol and its WAL read helpers.
    Compaction reads the latest WAL fragments and
    applies them to the DB state (indexes etc) and
    publishes that state on S3. This spec uses a more
    abstract checkpoint as this published state.
*)

\* ****************************************************
\* HELPERS
\* ****************************************************

LocalCheckpointPos(r) ==
    IF rCompCheckpoint[r].snapshot = <<>> THEN 0
    ELSE Last(rCompCheckpoint[r].snapshot).pos

EndCompaction(r) ==
    /\ rCompState' = [rCompState EXCEPT ![r] = IDLE]
    /\ rCompCheckpoint' = [rCompCheckpoint EXCEPT ![r] = None]
    /\ rCompCursor' = [rCompCursor EXCEPT ![r] = None]

\* ****************************************************
\* COMPACTION ACTIONS
\* ****************************************************

(* ---------------------------------------------------------
    ACTION: CompactorStart (step 1)

    The compactor loads the published checkpoint and
    transitions to REPLAY_WAL.

    Note: To reduce state space, this only triggers
    when the WAL has advanced past the current checkpoint.
-----------------------------------------------------------*)

TriggerCompaction(r) ==
    /\ rCompState[r] = IDLE
    /\ rManifest[r] /= None \* WAL writer opened
    \* something to checkpoint (not in impl)
    /\ NextSeqNo(rManifest[r])-1  > checkpoint.seqNo 

CompactorStart(r) ==
    /\ TriggerCompaction(r)
    /\ rCompCheckpoint' = [rCompCheckpoint EXCEPT ![r] = checkpoint]
    /\ rCompState' = [rCompState EXCEPT ![r] = REPLAY_WAL]
    /\ UNCHANGED <<storeVars, auxVars, repSharedVars, repWriterVars, repGcVars,
                   rCompCursor>>

(* ---------------------------------------------------------
    ACTION: CompactorReplayWAL (step 2)

    The compactor replays one fragment into its ongoing
    checkpoint state. The action repeats until it reaches
    the end of the WAL.

    If an fragment file is not found, compaction aborts.
    If we've reached the end of the WAL, transition to
    COMMIT_CHECKPOINT.
    Else, apply the fragment.
-----------------------------------------------------------*)

CompactorReplayWAL(r) ==
    /\ rCompState[r] = REPLAY_WAL
    /\ LET nextSeqNo == rCompCheckpoint[r].seqNo + 1
           frag      == WalRead(r, nextSeqNo)
       IN
          CASE 
            \* CASE 1: Expected fragment not found
               frag = NotFound -> EndCompaction(r)
            \* CASE 2: No fragment, reached end of WAL
            [] frag = None ->
                /\ rCompState' = [rCompState EXCEPT ![r] = COMMIT_CHECKPOINT]
                /\ UNCHANGED <<rCompCheckpoint, rCompCursor>>
            \* CASE 3: Fragment read, apply to ongoing cp
            [] OTHER ->
                /\ rCompCheckpoint' = [rCompCheckpoint EXCEPT 
                                            ![r].snapshot = @ \o frag.entries,
                                            ![r].seqNo    = frag.seqNo]
                /\ UNCHANGED <<rCompState, rCompCursor>>
    /\ UNCHANGED <<storeVars, auxVars, repSharedVars, repWriterVars, repGcVars>>

(* ---------------------------------------------------------
    ACTION: CompactorCommitCheckpoint (step 3)

    The compactor publishes its checkpoint by CAS.
    On CAS conflict, abort compaction.
    On success, transition to READ_CURSOR (first step
    in advancing the compaction cursor).
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
                   auxVars, repSharedVars, repWriterVars, repGcVars>>

(* ---------------------------------------------------------
    ACTION: CompactorReadCursor (step 4)

    The compactor reads the cursor on S3. 
    If the cursor already matches or exceeds the current
    checkpoint log position, then abort. Another compactor
    already ran.
    Else transition to COMMIT_CURSOR.
-----------------------------------------------------------*)

CompactorReadCursor(r) ==
    /\ rCompState[r] = READ_CURSOR
    /\ \/ /\ compCursor.pos >= LocalCheckpointPos(r)
          /\ EndCompaction(r)
       \/ /\ compCursor.pos < LocalCheckpointPos(r)
          /\ rCompCursor' = [rCompCursor EXCEPT ![r] = compCursor]
          /\ rCompState' = [rCompState EXCEPT ![r] = COMMIT_CURSOR]
          /\ UNCHANGED <<rCompCheckpoint>>
    /\ UNCHANGED <<storeVars, auxVars, repSharedVars, repWriterVars, repGcVars>>

(* ---------------------------------------------------------
    ACTION: CompactorCommitCursor (step 5)

    The compactor advances the cursor by CAS and ends the
    run, whether the CAS succeeds or conflicts.
-----------------------------------------------------------*)

CompactorCommitCursor(r) ==
    /\ rCompState[r] = COMMIT_CURSOR
    /\ IF rCompCursor[r].version = compCursor.version
       THEN compCursor' = [rCompCursor[r] EXCEPT 
                                !.pos     = LocalCheckpointPos(r),
                                !.version = @ + 1]
       ELSE UNCHANGED compCursor
    /\ EndCompaction(r)
    /\ UNCHANGED <<manifest, fragments, checkpoint, gcPlanFile,
                   auxVars, repSharedVars, repWriterVars, repGcVars>>

\* ****************************************************
\* Init, Next and Fairness
\* ****************************************************

CompactorInit ==
    /\ rCompState = [r \in Replicas |-> IDLE]
    /\ rCompCheckpoint = [r \in Replicas |-> None]
    /\ rCompCursor = [r \in Replicas |-> None]

CompactorNext(r) ==
    \/ CompactorStart(r)
    \/ CompactorReplayWAL(r)
    \/ CompactorCommitCheckpoint(r)
    \/ CompactorReadCursor(r)
    \/ CompactorCommitCursor(r)

CompactorFairness(r) ==
    /\ WF_vars(CompactorStart(r))
    /\ WF_vars(CompactorReplayWAL(r))
    /\ WF_vars(CompactorCommitCheckpoint(r))
    /\ WF_vars(CompactorReadCursor(r))
    /\ WF_vars(CompactorCommitCursor(r))

=============================================================================
