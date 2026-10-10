----------------------------- MODULE Wal3Writer -----------------------------

EXTENDS Wal3Common

\* WAL append and recovery protocol.

\* ****************************************************
\* HELPERS
\* ****************************************************

UpdateWriterFromManifest(r, m) ==
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
        /\ UpdateWriterFromManifest(r, manifest0)
        /\ auxCommitted' = auxCommitted \o f.entries
        /\ UNCHANGED rManifestLocked

NoCommit == UNCHANGED <<manifest, repSharedVars, rWriterFragment,
                        rWriterNextPos, rWriterNextSeqNo, auxCommitted>>

\* ****************************************************
\* WAL APPEND ACTIONS
\* ****************************************************

(* ---------------------------------------------------------
    ACTION: WalRefreshManifest

    DESC TODO
-----------------------------------------------------------*)

WalRefreshManifest(r) ==
    /\ \/ rWriterState[r] \in {IDLE, REFRESH}
       \/ /\ rWriterState[r] = READY
          /\ rManifest[r].version < manifest.version
    /\ ~IsManifestLocked(r)
    /\ rManifest' = [rManifest EXCEPT ![r] = manifest]
    /\ rWriterState' = [rWriterState EXCEPT ![r] = RECOVER]
    /\ UpdateWriterFromManifest(r, manifest)
    /\ UNCHANGED <<storeVars, auxVars, repGcVars, repCompVars,
                   rWriterPendingValues, rManifestLocked>>

(* ---------------------------------------------------------
    ACTION: WalRecover

    DESC TODO
-----------------------------------------------------------*)

DoingWrite(r) == rWriterPendingValues[r] /= {}

PostRefreshState(r) ==
    IF DoingWrite(r) THEN UPLOAD_FRAGMMENT
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

    DESC TODO
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

    DESC TODO
-----------------------------------------------------------*)

WalAcceptWrites(r, values) ==
    /\ rWriterState[r] = READY
    /\ Cardinality(values) > 0
    /\ \A v \in values : v \notin auxUsedValues
    /\ rWriterPendingValues' = [rWriterPendingValues EXCEPT ![r] = values]
    /\ rWriterState' = [rWriterState EXCEPT ![r] = UPLOAD_FRAGMMENT]
    /\ auxUsedValues' = auxUsedValues \union values
    /\ UNCHANGED <<storeVars, auxCommitted, repGcVars, repCompVars,
                   repSharedVars, rWriterFragment, rWriterNextPos,
                   rWriterNextSeqNo>>

(* ---------------------------------------------------------
    ACTION: WalUploadFragment

    DESC TODO
-----------------------------------------------------------*)

WalUploadFragment(r) ==
    /\ rWriterState[r] = UPLOAD_FRAGMMENT
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

    DESC TODO
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

WriterNext(r) ==
    \/ WalRefreshManifest(r)
    \/ WalRecover(r)
    \/ WalCommitRecoveredFragment(r)
    \/ \E values \in SUBSET Values : WalAcceptWrites(r, values)
    \/ WalUploadFragment(r)
    \/ WalCommitFragment(r)

=============================================================================
