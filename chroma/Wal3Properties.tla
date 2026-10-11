----------------------------- MODULE Wal3Properties -----------------------------

EXTENDS Wal3Common

Symmetry ==
      Permutations(Replicas)
          \union Permutations(Values)

\* ****************************************************
\* PROPERTIES
\* ****************************************************

\* INV: ValidReplicas
\* Preemption applies to writer and GC at the same time
\* There must be at least one functional wal writer
\* and no wal writer entered an illegal state
ValidReplicas ==
    /\ \A r \in Replicas :
        /\ rWriterState[r] = PREEMPTED => rGcState[r] = PREEMPTED
        /\ rWriterState[r] /= ILLEGAL_STATE
    /\ \E r \in Replicas : rWriterState[r] /= PREEMPTED
    
\* INV: ValidFragments
\* Both fragments and fragment refs are contiguous (no
\* gaps, no overlap) and fragment refs are consistent with fragments
ValidFragments ==
    \* Fragment refs are contiguous
    /\ ~\E i, j \in DOMAIN manifest.fragRefs :
        /\ i + 1 = j
        /\ manifest.fragRefs[i].limit /= manifest.fragRefs[j].start
        /\ manifest.fragRefs[i].seqNo + 1 = manifest.fragRefs[j].seqNo
    \* Fragment refs point to written fragment addresses and their 
    \* bounds match
    /\ \A i \in DOMAIN manifest.fragRefs :
        LET ref  == manifest.fragRefs[i]
            frag == fragments[ref.seqNo]
        IN
            \* fragment exists
            /\ ref.seqNo \in DOMAIN fragments
            \* bounds match
            /\ ref.start = MinLogPos(fragments[ref.seqNo])
            /\ ref.limit -1 = MaxLogPos(fragments[ref.seqNo])
            \* positions are sequential
            /\ \A j \in 1..Len(frag.entries)-1 :
                frag.entries[j].pos + 1 = frag.entries[j+1].pos

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
        /\ \A i \in DOMAIN manifest.fragRefs :
            LET ref == manifest.fragRefs[i]
            IN /\ ref.seqNo \in DOMAIN fragments
               /\ ref.start >= 1
               /\ ref.limit <= Len(auxCommitted) + 1
               /\ fragments[ref.seqNo].entries =
                       SubSeq(auxCommitted, ref.start, ref.limit - 1)

\* LIVENESS: AllValuesAttempted
\* Every writable value has a write attempt
AllValuesAttempted ==
    <>[](auxUsedValues = Values)

\* LIVENESS: OpsEventuallyComplete
\* Every role (writer, gc, compaction) reaches a termination state
OpsEventuallyComplete ==
    \A r \in Replicas :
        /\ rWriterState[r] /= IDLE ~> rWriterState[r] \in {READY, PREEMPTED}
        /\ rGcState[r] /= IDLE ~> rGcState[r] \in {IDLE, PREEMPTED, ABORTED}
        /\ rCompState[r] /= IDLE ~> rCompState[r] = IDLE

\* LIVENESS: GcEventuallyAdvances
\* GC eventually advances to the compaction cursor
\* This is assessed by checking the floor log pos in the
\* manifest against the compaction cursor log pos.

WalLogPosFloor ==
    IF manifest.fragRefs = <<>> THEN manifest.initialPos
    ELSE Head(manifest.fragRefs).start

\* The position is covered by the checkpoint
CollectiblePosition(pos) ==
    \E i \in DOMAIN manifest.fragRefs :
        LET f == manifest.fragRefs[i]
        IN /\ pos >= f.start
           /\ pos < f.limit
           /\ f.limit <= compCursor.pos + 1

GcEventuallyAdvances ==
    \A pos \in 1..Cardinality(Values) :
        CollectiblePosition(pos) ~> (WalLogPosFloor > pos)

=============================================================================
