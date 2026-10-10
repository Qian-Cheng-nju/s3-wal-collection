----------------------------- MODULE Wal3Compactor -----------------------------

EXTENDS Wal3Common

\* Compaction protocol and its WAL read helpers. 
\* Reads use the shared cached manifest.

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
    ACTION: CompactorStart

    DESC TODO
-----------------------------------------------------------*)

\* Trigger when no compaction running and WAL has
\* started. Also to reduce state space, only trigger
\* when the WAL has advanced past the current checkpoint
TriggerCompaction(r) ==
    /\ rCompState[r] = IDLE
    /\ rManifest[r] /= None \* WAL writer opened
    /\ NextSeqNo(rManifest[r])-1  > checkpoint.seqNo

CompactorStart(r) ==
    /\ TriggerCompaction(r)
    /\ rCompCheckpoint' = [rCompCheckpoint EXCEPT ![r] = checkpoint]
    /\ rCompState' = [rCompState EXCEPT ![r] = REPLAY_WAL]
    /\ UNCHANGED <<storeVars, auxVars, repSharedVars, repWriterVars, repGcVars,
                   rCompCursor>>

(* ---------------------------------------------------------
    ACTION: CompactorReplayWAL

    DESC TODO
-----------------------------------------------------------*)

CompactorReplayWAL(r) ==
    /\ rCompState[r] = REPLAY_WAL
    /\ LET nextSeqNo == rCompCheckpoint[r].seqNo + 1
           frag      == WalRead(r, nextSeqNo)
       IN
          CASE frag = NotFound -> EndCompaction(r)
            [] frag = None ->
                /\ rCompState' = [rCompState EXCEPT ![r] = COMMIT_CHECKPOINT]
                /\ UNCHANGED <<rCompCheckpoint, rCompCursor>>
            [] OTHER ->
                /\ rCompCheckpoint' = [rCompCheckpoint EXCEPT 
                                            ![r].snapshot = @ \o frag.entries,
                                            ![r].seqNo    = frag.seqNo]
                /\ UNCHANGED <<rCompState, rCompCursor>>
    /\ UNCHANGED <<storeVars, auxVars, repSharedVars, repWriterVars, repGcVars>>

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
                   auxVars, repSharedVars, repWriterVars, repGcVars>>

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
    /\ UNCHANGED <<storeVars, auxVars, repSharedVars, repWriterVars, repGcVars>>

(* ---------------------------------------------------------
    ACTION: CompactorCommitCursor

    DESC TODO
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

CompactorNext(r) ==
    \/ CompactorStart(r)
    \/ CompactorReplayWAL(r)
    \/ CompactorCommitCheckpoint(r)
    \/ CompactorReadCursor(r)
    \/ CompactorCommitCursor(r)

=============================================================================
