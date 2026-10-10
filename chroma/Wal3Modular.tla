----------------------------- MODULE Wal3Modular -----------------------------

EXTENDS Wal3Writer, Wal3GC, Wal3Compactor, Wal3Properties

Init ==
    /\ manifest = [fragRefs     |-> <<>>,
                   initialSeqNo |-> 1,
                   initialPos   |-> 1,
                   version      |-> 0]
    /\ fragments = <<>>
    /\ checkpoint = [seqNo |-> 0, snapshot |-> <<>>, version |-> 1]
    /\ compCursor = [pos |-> 0, version |-> 1]
    /\ gcPlanFile = [seqNoLimit |-> 0, version |-> 1]
    /\ rManifest = [r \in Replicas |-> None]
    /\ rManifestLocked = [r \in Replicas |-> FALSE]
    /\ rWriterState = [r \in Replicas |-> IDLE]
    /\ rWriterPendingValues = [r \in Replicas |-> {}]
    /\ rWriterFragment = [r \in Replicas |-> None]
    /\ rWriterNextPos = [r \in Replicas |-> 0]
    /\ rWriterNextSeqNo = [r \in Replicas |-> 0]
    /\ rGcState = [r \in Replicas |-> IDLE]
    /\ rGcCachedPlan = [r \in Replicas |-> None]
    /\ rGcPinnedPlan = [r \in Replicas |-> None]
    /\ rGcTrimLimit = [r \in Replicas |-> 0]
    /\ rGcCompCursor = [r \in Replicas |-> None]
    /\ rCompState = [r \in Replicas |-> IDLE]
    /\ rCompCheckpoint = [r \in Replicas |-> None]
    /\ rCompCursor = [r \in Replicas |-> None]
    /\ auxUsedValues = {}
    /\ auxCommitted = <<>>

Next ==
    \E r \in Replicas :
        \/ WriterNext(r)
        \/ GcNext(r)
        \/ CompactorNext(r)

\* Preserve fairness for each individual action, using the full state tuple.
Fairness ==
    \A r \in Replicas :
        /\ WF_vars(WalRefreshManifest(r))
        /\ WF_vars(WalRecover(r))
        /\ WF_vars(WalCommitRecoveredFragment(r))
        /\ \A values \in SUBSET Values : WF_vars(WalAcceptWrites(r, values))
        /\ WF_vars(WalUploadFragment(r))
        /\ WF_vars(WalCommitFragment(r))
        /\ WF_vars(GcPhase1ReadCursor(r))
        /\ WF_vars(GcPhase1ReadGcFile(r))
        /\ WF_vars(GcPhase1ComputePlan(r))
        /\ WF_vars(GcPhase2ReadGcFile(r))
        /\ WF_vars(GcPhase2CasManifest(r))
        /\ WF_vars(GcPhase3ReadGcFile(r))
        /\ WF_vars(GcPhase3ReadManifest(r))
        /\ WF_vars(GcPhase3Delete(r))
        /\ WF_vars(GcPhase3Complete(r))
        \* /\ WF_vars(CompactorStart(r))
        /\ WF_vars(CompactorReplayWAL(r))
        /\ WF_vars(CompactorCommitCheckpoint(r))
        /\ WF_vars(CompactorReadCursor(r))
        /\ WF_vars(CompactorCommitCursor(r))

Spec == Init /\ [][Next]_vars
LivenessSpec == Init /\ [][Next]_vars /\ Fairness

=============================================================================
