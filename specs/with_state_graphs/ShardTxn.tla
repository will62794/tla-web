--------------------------- MODULE ShardTxn ---------------------------------
(**************************************************************************)
(* Pluscal algoritm for a simple key-value store with snapshot isolation  *)
(**************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, Util, TLC

CONSTANTS Keys, Values, NoValue, STMTS
CONSTANTS WC, RC

TxId == Values           \* The set of all transaction IDs

\* Instantiating ClientCentric enables us to check transaction isolation guarantees
\* https://muratbuffalo.blogspot.com/2022/07/automated-validation-of-state-based.html         
CC == INSTANCE ClientCentric WITH Keys <- Keys, Values <- TxId \union {NoValue}          

\* for instantiating the ClientCentric module
wOp(k,v) == CC!w(k,v)
rOp(k,v) == CC!r(k,v)    
InitialState == [k \in Keys |-> NoValue]   

(* --SNAPSHOT_algorithm KVsnap {

variables 
    \* The set of open snapshot transactions
    tx = {};

    \* The set of local updates each txn makes
    updated = [t \in TxId |-> {}];
    \* Txns that overlapped with each txn at any point 
    overlap = [t \in TxId |-> {}];   

    \* Router writes to rlog, txns scan rlog to learn stmts
    rlog = [t \in TxId |->  <<>>];
    \* Signal aborted txns to the router        
    aborted = [t \in TxId |-> FALSE]; 

    \* MDB init
    log = <<>>; 
    commitIndex = 0; 
    epoch = 1;

define {
    MDB == INSTANCE MDB
    ASSUME WC \in MDB!WCVALUES
    ASSUME RC \in MDB!RCVALUES

    Ops == {"read", "write"}
    Entry == [k: Keys, op: Ops]
    CreateEntry(k, op) == [k |-> k, op |-> op] 

    \* See end of file for invariants
}

fair process (Router = "Router")
variables
    \* track statements in each txn
    rtxn = [t \in TxId |-> 0]; 
{
ROUTER: \*   
    while ( \E t \in TxId: rtxn[t] < STMTS /\ ~aborted[t] ) {
        with (  t = CHOOSE t \in TxId: rtxn[t] < STMTS /\ ~aborted[t];
                k \in Keys;
                op \in Ops) { 
            rlog[t]:= Append(rlog[t], CreateEntry(k, op));
            rtxn[t] := rtxn[t]+1;
        }
    }
}    


\* Transaction processing
fair process (t \in TxId)
variables
    lsn = 0;  \* tracks which statement in txn
    snapshotStore = [k \in Keys |-> NoValue];   \* local snapshot of the store
    ops = <<>>;     \* reads & writes txn executes; used for interfacing to CC
{
TXN:  
    while ( lsn < STMTS /\ ~aborted[self] ){
        await lsn < Len(rlog[self]); \* router log has new stmt for me
        lsn := lsn + 1;
        if ( lsn = 1 ) { \* initialize txn if first statement
            tx := tx \union {self};
            snapshotStore := \* take my snapshot of MDB
                [k \in Keys |-> (CHOOSE read \in MDB!Read(k) : TRUE).value];
            overlap := [t \in TxId |-> IF t = self THEN tx 
                                       ELSE IF t \in tx THEN overlap[t] \union {self} 
                                            ELSE overlap[t]];
        };       

READ: 
        with (  op = rlog[self][lsn].op; 
                k = rlog[self][lsn].k; ){
            if (op = "read") {
                \* log read for CC isolation check 
                ops := Append( ops, rOp(k, snapshotStore[k]) );
                goto TXN; 
            }; 
        }; 

WRITE:            
        with (  op = rlog[self][lsn].op; 
                k = rlog[self][lsn].k; ){        
            \* perform write on my snapshot if there is no conflict with a non-aborted txn
            if ( \A t \in overlap[self] \ {self}: k \notin updated[t] ) {
                updated[self] := updated[self] \union {k}; 
                snapshotStore[k] := self;
                \* log write for CC isolation check 
                ops := Append( ops, wOp(k, self) );  

                if ( lsn = STMTS ) { \* end of txn, so COMMIT
                    \* update MDB by writing to logs directly/atomically
                    log := log \o SetToSeq({ [key |-> key, value |-> self]: key \in updated[self]});  
                    commitIndex :=  Len(log);
                    tx := tx \ {self};  \* take self off of active txn set
                };
            } else { \* abort
                    tx := tx \ {self};  \* take self off of active txn set
                    aborted[self] := TRUE;
                    updated[self] := {};
                    ops := <<>>; \* update CC view because the txn is aborted
            };
        }
    } \* end while
}


}
*)

\* BEGIN TRANSLATION (chksum(pcal) = "32fa2d41" /\ chksum(tla) = "ccc58da9")
VARIABLES tx, updated, overlap, rlog, aborted, log, commitIndex, epoch, pc

(* define statement *)
MDB == INSTANCE MDB
ASSUME WC \in MDB!WCVALUES
ASSUME RC \in MDB!RCVALUES

Ops == {"read", "write"}
Entry == [k: Keys, op: Ops]
CreateEntry(k, op) == [k |-> k, op |-> op]

VARIABLES rtxn, lsn, snapshotStore, ops

vars == << tx, updated, overlap, rlog, aborted, log, commitIndex, epoch, pc, 
           rtxn, lsn, snapshotStore, ops >>

ProcSet == {"Router"} \cup (TxId)

Init == (* Global variables *)
        /\ tx = {}
        /\ updated = [t \in TxId |-> {}]
        /\ overlap = [t \in TxId |-> {}]
        /\ rlog = [t \in TxId |->  <<>>]
        /\ aborted = [t \in TxId |-> FALSE]
        /\ log = <<>>
        /\ commitIndex = 0
        /\ epoch = 1
        (* Process Router *)
        /\ rtxn = [t \in TxId |-> 0]
        (* Process t *)
        /\ lsn = [self \in TxId |-> 0]
        /\ snapshotStore = [self \in TxId |-> [k \in Keys |-> NoValue]]
        /\ ops = [self \in TxId |-> <<>>]
        /\ pc = [self \in ProcSet |-> CASE self = "Router" -> "ROUTER"
                                        [] self \in TxId -> "TXN"]

ROUTER == /\ pc["Router"] = "ROUTER"
          /\ IF \E t \in TxId: rtxn[t] < STMTS /\ ~aborted[t]
                THEN /\ LET t == CHOOSE t \in TxId: rtxn[t] < STMTS /\ ~aborted[t] IN
                          \E k \in Keys:
                            \E op \in Ops:
                              /\ rlog' = [rlog EXCEPT ![t] = Append(rlog[t], CreateEntry(k, op))]
                              /\ rtxn' = [rtxn EXCEPT ![t] = rtxn[t]+1]
                     /\ pc' = [pc EXCEPT !["Router"] = "ROUTER"]
                ELSE /\ pc' = [pc EXCEPT !["Router"] = "Done"]
                     /\ UNCHANGED << rlog, rtxn >>
          /\ UNCHANGED << tx, updated, overlap, aborted, log, commitIndex, 
                          epoch, lsn, snapshotStore, ops >>

Router == ROUTER

TXN(self) == /\ pc[self] = "TXN"
             /\ IF lsn[self] < STMTS /\ ~aborted[self]
                   THEN /\ lsn[self] < Len(rlog[self])
                        /\ lsn' = [lsn EXCEPT ![self] = lsn[self] + 1]
                        /\ IF lsn'[self] = 1
                              THEN /\ tx' = (tx \union {self})
                                   /\ snapshotStore' = [snapshotStore EXCEPT ![self] = [k \in Keys |-> (CHOOSE read \in MDB!Read(k) : TRUE).value]]
                                   /\ overlap' = [t \in TxId |-> IF t = self THEN tx'
                                                                 ELSE IF t \in tx' THEN overlap[t] \union {self}
                                                                      ELSE overlap[t]]
                              ELSE /\ TRUE
                                   /\ UNCHANGED << tx, overlap, snapshotStore >>
                        /\ pc' = [pc EXCEPT ![self] = "READ"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ UNCHANGED << tx, overlap, lsn, snapshotStore >>
             /\ UNCHANGED << updated, rlog, aborted, log, commitIndex, epoch, 
                             rtxn, ops >>

READ(self) == /\ pc[self] = "READ"
              /\ LET op == rlog[self][lsn[self]].op IN
                   LET k == rlog[self][lsn[self]].k IN
                     IF op = "read"
                        THEN /\ ops' = [ops EXCEPT ![self] = Append( ops[self], rOp(k, snapshotStore[self][k]) )]
                             /\ pc' = [pc EXCEPT ![self] = "TXN"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "WRITE"]
                             /\ ops' = ops
              /\ UNCHANGED << tx, updated, overlap, rlog, aborted, log, 
                              commitIndex, epoch, rtxn, lsn, snapshotStore >>

WRITE(self) == /\ pc[self] = "WRITE"
               /\ LET op == rlog[self][lsn[self]].op IN
                    LET k == rlog[self][lsn[self]].k IN
                      IF \A t \in overlap[self] \ {self}: k \notin updated[t]
                         THEN /\ updated' = [updated EXCEPT ![self] = updated[self] \union {k}]
                              /\ snapshotStore' = [snapshotStore EXCEPT ![self][k] = self]
                              /\ ops' = [ops EXCEPT ![self] = Append( ops[self], wOp(k, self) )]
                              /\ IF lsn[self] = STMTS
                                    THEN /\ log' = log \o SetToSeq({ [key |-> key, value |-> self]: key \in updated'[self]})
                                         /\ commitIndex' = Len(log')
                                         /\ tx' = tx \ {self}
                                    ELSE /\ TRUE
                                         /\ UNCHANGED << tx, log, commitIndex >>
                              /\ UNCHANGED aborted
                         ELSE /\ tx' = tx \ {self}
                              /\ aborted' = [aborted EXCEPT ![self] = TRUE]
                              /\ updated' = [updated EXCEPT ![self] = {}]
                              /\ ops' = [ops EXCEPT ![self] = <<>>]
                              /\ UNCHANGED << log, commitIndex, snapshotStore >>
               /\ pc' = [pc EXCEPT ![self] = "TXN"]
               /\ UNCHANGED << overlap, rlog, epoch, rtxn, lsn >>

t(self) == TXN(self) \/ READ(self) \/ WRITE(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Router
           \/ (\E self \in TxId: t(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Router)
        /\ \A self \in TxId : WF_vars(t(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


TypeOK == \* type invariant
    /\ tx \subseteq TxId
    /\ updated \in [TxId -> SUBSET Keys]
    /\ \A t1,t2 \in TxId: t1 \in overlap[t2] => t2 \in overlap[t1] 

\* Snapshot isolation invariant
SnapshotIsolation == CC!SnapshotIsolation(InitialState, Range(ops))

\* Serializability would not be satisfied due to write-skew
Serialization == CC!Serializability(InitialState, Range(ops))

TxIdSymmetric == Permutations(TxId)

\* LogIndicesImpl == 1..4

\* CheckpointsImpl == LogIndicesImpl \cup {0}

\* EpochsImpl == 1..3

\* SpecificStateSpace ==
\*     /\ epoch < EpochMax

BaitLog == 
    /\ TRUE
    \* /\ commitIndex < 5
    \* /\ Len(log) < 6
    
\* Alias == [
\*     log |-> log,
\*     commitIndex |-> commitIndex,
\*     readIndex |-> readIndex,
\*     epoch |-> epoch
\* ]
===========================================================================
