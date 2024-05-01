---- MODULE SingleNode1 ----

EXTENDS Naturals, Sequences, SequencesExt

RwTxRequest == "RwTxRequest"
RwTxResponse == "RwTxResponse"
RoTxRequest == "RoTxRequest"
RoTxResponse == "RoTxResponse"
TxStatusReceived == "TxStatusReceived"

CommittedStatus == "CommittedStatus"
InvalidStatus == "InvalidStatus"
TxStatuses == {
    CommittedStatus,
    InvalidStatus
    }

FirstBranch == 1

Views == Nat

\* Sequence numbers start at 1, 0 is used a null value
SeqNums == Nat

\* TxIDs consist of a view and sequence number and thus start at (1,1)
TxIDs == Views \X SeqNums

\* This models uses a dummy application where read-write transactions 
\* append an integer to a list and then reads the list
\* Read-only transactions simply read the list
Txs == Nat

VARIABLES history

HistoryTypeOK ==
    \A i \in DOMAIN history:
        \/  /\ history[i].type \in {RwTxRequest, RoTxRequest}
            /\ history[i].tx \in Txs
        \/  /\ history[i].type \in {RwTxResponse, RoTxResponse}
            /\ history[i].tx \in Txs
            /\ history[i].observed \in Seq(Txs)
            /\ history[i].tx_id \in TxIDs
        \/  /\ history[i].type = TxStatusReceived
            /\ history[i].tx_id \in TxIDs
            /\ history[i].status \in TxStatuses

\* Abstract ledgers that contains only client transactions (no signatures)
\* Indexed by view, each ledger is the ledger associated with leader of that view 
\* In practice, the ledger of every CCF node is one of these or a prefix for one of these
\* This could be switched to a tree which can represent forks more elegantly
VARIABLES ledgerBranches

LedgerTypeOK ==
    \A view \in DOMAIN ledgerBranches:
        \A seqnum \in DOMAIN ledgerBranches[view]:
            \* Each ledger entry is tuple containing a view and tx
            \* The ledger entry index is the sequence number
            /\ ledgerBranches[view][seqnum].view \in Views
            /\ "tx" \in DOMAIN ledgerBranches[view][seqnum] => ledgerBranches[view][seqnum].tx \in Txs

\* In this abstract version of CCF's consensus layer, each ledger is append-only
LedgersMonoProp ==
    [][\A view \in DOMAIN ledgerBranches: IsPrefix(ledgerBranches[view], ledgerBranches'[view])]_ledgerBranches

vars == << history, ledgerBranches >>

TypeOK ==
    /\ HistoryTypeOK
    /\ LedgerTypeOK

Init ==
    /\ history = <<>>
    /\ ledgerBranches = [ x \in 1..FirstBranch |-> <<>>]

IndexOfLastRequested ==
    SelectLastInSeq(history, LAMBDA e : e.type \in {RwTxRequest, RoTxRequest})

NextRequestId ==
    IF IndexOfLastRequested = 0 THEN 0 ELSE history[IndexOfLastRequested].tx+1

\* Submit new read-write transaction
\* This could be extended to add a notion of session and then check for session consistency
RwTxRequestAction ==
    /\ history' = Append(
        history, 
        [type |-> RwTxRequest, tx |-> NextRequestId]
        )
    /\ UNCHANGED ledgerBranches

\* Execute a read-write transaction
RwTxExecuteAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxRequest
        \* Check transaction has not already been added to a ledger
        /\ \A view \in DOMAIN ledgerBranches: 
            \A seqnum \in DOMAIN ledgerBranches[view]: 
                "tx" \in DOMAIN ledgerBranches[view][seqnum]
                => history[i].tx /= ledgerBranches[view][seqnum].tx
        \* Note that a transaction can be added to any ledger, simulating the fact
        \* that it can be picked up by the current leader or any former leader
        /\ \E view \in FirstBranch..Len(ledgerBranches):
                ledgerBranches' = [ledgerBranches EXCEPT ![view] = 
                    Append(@,[view |-> view, tx |-> history[i].tx])]
        /\ UNCHANGED history

LedgerBranchTxOnly(branch) ==
    LET SubBranch == SelectSeq(branch, LAMBDA e : "tx" \in DOMAIN e)
    IN [i \in DOMAIN SubBranch |-> SubBranch[i].tx]

\* Response to a read-write transaction
RwTxResponseAction ==
    /\ \E i \in DOMAIN history :
        \* Check request has been received and executed but not yet responded to
        /\ history[i].type = RwTxRequest
        /\ {j \in DOMAIN history: 
            /\ j > i 
            /\ history[j].type = RwTxResponse
            /\ history[j].tx = history[i].tx} = {}
        /\ \E view \in FirstBranch..Len(ledgerBranches):
            /\ \E seqnum \in DOMAIN ledgerBranches[view]: 
                /\ "tx" \in DOMAIN ledgerBranches[view][seqnum]
                /\ history[i].tx = ledgerBranches[view][seqnum].tx
                /\ history' = Append(
                    history,[
                        type |-> RwTxResponse, 
                        tx |-> history[i].tx, 
                        observed |-> LedgerBranchTxOnly(SubSeq(ledgerBranches[view],1,seqnum)),
                        tx_id |-> <<ledgerBranches[view][seqnum].view, seqnum>>] )
    /\ UNCHANGED ledgerBranches

\* Sending a committed status message
\* Note that a request could only be committed if it's in the highest view's ledger
StatusCommittedResponseAction ==
    /\ \E i \in DOMAIN history :
        LET view == history[i].tx_id[1]
            seqno == history[i].tx_id[2]
        IN /\ history[i].type = RwTxResponse
           /\ Len(Last(ledgerBranches)) >= seqno
           /\ Last(ledgerBranches)[seqno].view = view
           \* There is no future InvalidStatus that's incompatible with this commit
           \* This is to accomodate StatusInvalidResponseAction making future commits invalid,
           \* and is an unnecessary complication for model checking. It does facilitate trace
           \* validation though, by allowing immediate processing of Invalids without
           \* needing to wait for the commit history knowledge to catch up.
           /\ \lnot \E j \in DOMAIN history:
                /\ history[j].type = TxStatusReceived
                /\ history[j].status = InvalidStatus
                /\ history[j].tx_id[1] = view
                /\ history[j].tx_id[2] <= seqno
           \* Reply
           /\ history' = Append(
              history,[
                type |-> TxStatusReceived, 
                tx_id |-> history[i].tx_id,
                status |-> CommittedStatus]
              )
    /\ UNCHANGED ledgerBranches

\* Append a transaction to the ledger which does not impact the state we are considering
AppendOtherTxnAction ==
    /\ \E view \in FirstBranch..Len(ledgerBranches):
        ledgerBranches' = [ledgerBranches EXCEPT ![view] = 
                    Append(@,[view |-> view])]
    /\ UNCHANGED history

\* A CCF service with a single node will never have a view change
\* so the log will never be rolled back and thus transaction IDs cannot be invalid
Next ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \* \/ StatusCommittedResponseAction
    \/ AppendOtherTxnAction
====