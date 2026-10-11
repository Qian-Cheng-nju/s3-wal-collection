----------------------------- MODULE Wal3Writer -----------------------------

EXTENDS Wal3Common

(* 
    WAL writer logic: append and recovery protocol.
*)

\* ****************************************************
\* HELPERS
\* ****************************************************

ResetAppendPosition(r, m) ==
    /\ rWriterFragment' = [rWriterFragment EXCEPT ![r] = None]
    /\ rWriterNextPos' = [rWriterNextPos EXCEPT ![r] = NextPos(m)]
    /\ rWriterNextSeqNo' = [rWriterNextSeqNo EXCEPT ![r] = NextSeqNo(m)]

CommitFragment(r) ==
    LET m         == rManifest[r]
        f         == rWriterFragment[r]
        fragRef   == FragRef(f)
        manifest0 == [m EXCEPT !.fragRefs = Append(@, fragRef),
                               !.version  = @ + 1]
    IN
        /\ manifest' = manifest0
        /\ rManifest' = [rManifest EXCEPT ![r] = manifest0]
        /\ ResetAppendPosition(r, manifest0)
        /\ auxCommitted' = auxCommitted \o f.entries
        /\ UNCHANGED rManifestLocked

NoCommit == UNCHANGED <<manifest, repSharedVars, rWriterFragment,
                        rWriterNextPos, rWriterNextSeqNo, auxCommitted>>

\* ****************************************************
\* WAL APPEND ACTIONS
\* ****************************************************

(* ---------------------------------------------------------
    ACTION: WalRefreshManifest

    The writer reloads the manifest, resets its append
    position, and enters recovery.
-----------------------------------------------------------*)

WalRefreshManifest(r) ==
    /\ \/ rWriterState[r] \in {IDLE, REFRESH}
       \/ /\ rWriterState[r] = READY
          /\ rManifest[r].version < manifest.version
    /\ ~IsManifestLocked(r)
    /\ rManifest' = [rManifest EXCEPT ![r] = manifest]
    /\ rWriterState' = [rWriterState EXCEPT ![r] = RECOVER]
    /\ ResetAppendPosition(r, manifest)
    /\ UNCHANGED <<storeVars, auxVars, repGcVars, repCompVars,
                   rWriterPendingValues, rManifestLocked>>

(* ---------------------------------------------------------
    ACTION: WalRecover

    The writer checks the next fragment address (one
    address beyond the last manifest registered fragment).
    
    If a fragment exists, then this means another replica
    uploaded a fragment but has not yet committed it
    (by adding its ref to the manifest). This replica now
    transitions to COMMIT_RECOVERED to commit this
    fragment.
    
    If the address is free, then no recovery is needed.
    The next state depends on whether refresh/recovery was
    part of an ongoing write or not. If there is an ongoing
    write then the replica transitions to UPLOAD_FRAGMENT
    to continue the write process, else it transitions
    to READY where it can accept more writes.   
-----------------------------------------------------------*)

DoingWrite(r) == rWriterPendingValues[r] /= {}

PostRefreshState(r) ==
    IF DoingWrite(r) THEN UPLOAD_FRAGMENT
    ELSE READY

FragmentRead(seqNo) ==
    IF seqNo \in DOMAIN fragments
    THEN fragments[seqNo]
    ELSE None

WalRecover(r) ==
    /\ rWriterState[r] = RECOVER
    /\ LET frag == FragmentRead(rWriterNextSeqNo[r]) IN
        \/ /\ frag /= None
           /\ rWriterFragment' = [rWriterFragment EXCEPT ![r] = frag]
           /\ rWriterState' = [rWriterState EXCEPT ![r] = COMMIT_RECOVERED]
        \/ /\ frag = None
           /\ rWriterState' = [rWriterState EXCEPT ![r] = PostRefreshState(r)]
           /\ UNCHANGED rWriterFragment
    /\ UNCHANGED <<storeVars, auxVars, repSharedVars, repGcVars, repCompVars,
                   rWriterPendingValues, rWriterNextPos, rWriterNextSeqNo>>

(* ---------------------------------------------------------
    ACTION: WalCommitRecoveredFragment

    The recovered fragment is added to the manifest 
    and a CAS write is attempted.
    A CAS conflict sends the writer back to REFRESH.
    A success transitions the writer to READY
    or UPLOAD_FRAGMENT depending on whether an ongoing
    write is occurring or not.
-----------------------------------------------------------*)

WalCommitRecoveredFragment(r) ==
    /\ rWriterState[r] = COMMIT_RECOVERED
    /\ ~IsManifestLocked(r)
    /\ \/ /\ rManifest[r].version = manifest.version
          /\ CommitFragment(r)
          /\ rWriterState' = [rWriterState EXCEPT ![r] = PostRefreshState(r)]
       \/ /\ rManifest[r].version /= manifest.version
          /\ NoCommit
          /\ rWriterState' = [rWriterState EXCEPT ![r] = REFRESH]
    /\ UNCHANGED <<fragments, checkpoint, compCursor, gcPlanFile,
                   auxUsedValues, repGcVars, repCompVars, rWriterPendingValues>>

(* ---------------------------------------------------------
    ACTION: WalAcceptWrites

    A ready writer accepts a nonempty batch of new values
    to write. The writer transitions to UPLOAD_FRAGMENT.
-----------------------------------------------------------*)

WalAcceptWrites(r, values) ==
    /\ rWriterState[r] = READY
    /\ Cardinality(values) > 0
    /\ \A v \in values : v \notin auxUsedValues
    /\ rWriterPendingValues' = [rWriterPendingValues EXCEPT ![r] = values]
    /\ rWriterState' = [rWriterState EXCEPT ![r] = UPLOAD_FRAGMENT]
    /\ auxUsedValues' = auxUsedValues \union values
    /\ UNCHANGED <<storeVars, auxCommitted, repGcVars, repCompVars,
                   repSharedVars, rWriterFragment, rWriterNextPos,
                   rWriterNextSeqNo>>

(* ---------------------------------------------------------
    ACTION: WalUploadFragment

    The writer uploads the batch as a fragment using
    put-if-absent. 
    The batch contains the pending values as an
    ordered sequence, with a log position for each
    entry.

    If put-if-absent fails then another writer has written
    to this address, so the writer transitions back to 
    REFRESH, else it transitions to COMMIT_FRAGMENT.
-----------------------------------------------------------*)

WalUploadFragment(r) ==
    /\ rWriterState[r] = UPLOAD_FRAGMENT
    /\ LET seq     == SetToSeq(rWriterPendingValues[r])
           entries == [i \in DOMAIN seq |->
                            [pos  |-> rWriterNextPos[r] + i - 1,
                             data |-> seq[i]]]
           frag    == [seqNo   |-> rWriterNextSeqNo[r],
                       entries |-> entries]
        IN
            \/ /\ frag.seqNo \in DOMAIN fragments
               /\ rWriterState' = [rWriterState EXCEPT ![r] = REFRESH]
               /\ UNCHANGED <<fragments, rWriterFragment>>
            \/ /\ frag.seqNo \notin DOMAIN fragments
               /\ fragments' = fragments @@ (frag.seqNo :> frag)
               /\ rWriterFragment' = [rWriterFragment EXCEPT ![r] = frag]
               /\ rWriterState' = [rWriterState EXCEPT ![r] = COMMIT_FRAGMENT]
    /\ UNCHANGED <<manifest, checkpoint, compCursor, gcPlanFile, auxVars,
                   repSharedVars, repGcVars, repCompVars, rWriterPendingValues,
                   rWriterNextPos, rWriterNextSeqNo>>

(* ---------------------------------------------------------
    ACTION: WalCommitFragment

    The writer commits the uploaded fragment by adding
    it to its cached manifest and performing a CAS write
    to the manifest in S3.
    A CAS conflict transitions the replica to PREEMPTED.
    This spec uses the PREEMPTED state to avoid an 
    infinite battle between replicas. In reality, it would
    cause the writer to stop and reopen.
    On write success, the writer transitions back to READY
    to be able to accept another write. Also the written
    fragment entries are recorded in auxCommitted for 
    invariant checking.
-----------------------------------------------------------*)

WalCommitFragment(r) ==
    /\ rWriterState[r] = COMMIT_FRAGMENT
    /\ ~IsManifestLocked(r)
    /\ \/ /\ rManifest[r].version = manifest.version
          /\ CommitFragment(r)
          /\ rWriterPendingValues' = [rWriterPendingValues EXCEPT ![r] = {}]
          /\ rWriterState' = [rWriterState EXCEPT ![r] = READY]
          /\ UNCHANGED rGcState
       \/ /\ rManifest[r].version /= manifest.version
          /\ NoCommit
          /\ PreemptWriterAndGc(r)
          /\ UNCHANGED <<rWriterPendingValues>>
    /\ UNCHANGED <<fragments, checkpoint, compCursor, gcPlanFile,
                   auxUsedValues, repCompVars,
                   rGcCachedPlan, rGcPinnedPlan, rGcTrimLimit, rGcCompCursor>>

\* ****************************************************
\* Init, Next and Fairness
\* ****************************************************

WriterInit ==
    /\ rWriterState = [r \in Replicas |-> IDLE]
    /\ rWriterPendingValues = [r \in Replicas |-> {}]
    /\ rWriterFragment = [r \in Replicas |-> None]
    /\ rWriterNextPos = [r \in Replicas |-> 0]
    /\ rWriterNextSeqNo = [r \in Replicas |-> 0]

\* The next state actions of the WAL writer
WriterNext(r) ==
    \/ WalRefreshManifest(r)
    \/ WalRecover(r)
    \/ WalCommitRecoveredFragment(r)
    \/ \E values \in SUBSET Values : WalAcceptWrites(r, values)
    \/ WalUploadFragment(r)
    \/ WalCommitFragment(r)

WriterFairness(r) ==
    /\ WF_vars(WalRefreshManifest(r))
    /\ WF_vars(WalRecover(r))
    /\ WF_vars(WalCommitRecoveredFragment(r))
    /\ \A values \in SUBSET Values : WF_vars(WalAcceptWrites(r, values))
    /\ WF_vars(WalUploadFragment(r))
    /\ WF_vars(WalCommitFragment(r))

=============================================================================
