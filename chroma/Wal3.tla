----------------------------- MODULE Wal3 -----------------------------

(*
    This spec is split up into the follow tla files:
    * Wal3 -> Init, Next and Spec
    * Wal3Writer -> The WAL writer (appends, recovery)
    * Wal3GC -> WAL GC task
    * Wal3Compactor -> WAL Compaction task
    * Wal3Common -> constants, variables, helpers, data model, typeok
    * WalProperties -> Safety and liveness properties

    This is a simplified model of Chroma's Wal3 protocol.
    Chroma DB state is represented by a checkpoint
    variable and the WAL is simplified based only
    on fragments (no snapshots).
*)

EXTENDS Wal3Writer, Wal3GC, Wal3Compactor, Wal3Properties

Init ==
    \* S3 state
    /\ manifest = [fragRefs     |-> <<>>,
                   initialSeqNo |-> 1,
                   initialPos   |-> 1,
                   version      |-> 0]
    /\ fragments = <<>>
    /\ checkpoint = [seqNo |-> 0, snapshot |-> <<>>, version |-> 1]
    /\ compCursor = [pos |-> 0, version |-> 1]
    /\ gcPlanFile = [seqNoLimit |-> 0, version |-> 1]
    \* Replica state
    /\ CommonInit
    /\ WriterInit
    /\ GcInit
    /\ CompactorInit
    \* Auxilliary state
    /\ auxUsedValues = {}
    /\ auxCommitted = <<>>

Next ==
    \E r \in Replicas :
        \/ WriterNext(r)
        \/ GcNext(r)
        \/ CompactorNext(r)

Fairness ==
    \A r \in Replicas :
        /\ WriterFairness(r)
        /\ GcFairness(r)
        /\ CompactorFairness(r)

Spec == Init /\ [][Next]_vars
LivenessSpec == Init /\ [][Next]_vars /\ Fairness

=============================================================================
