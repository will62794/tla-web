------------------------- MODULE SnapshotIsolation -------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

(**************************************************************************************************)
(*                                                                                                *)
(* This is a specification of snapshot isolation.  It is based on various sources, integrating    *)
(* ideas and definitions from:                                                                    *)
(*                                                                                                *)
(*     ``Making Snapshot Isolation Serializable", Fekete et al., 2005                             *)
(*     https://www.cse.iitb.ac.in/infolab/Data/Courses/CS632/2009/Papers/p492-fekete.pdf          *)
(*                                                                                                *)
(*     ``Serializable Isolation for Snapshot Databases", Cahill, 2009                             *)
(*     https://ses.library.usyd.edu.au/bitstream/2123/5353/1/michael-cahill-2009-thesis.pdf       *)
(*                                                                                                *)
(*     ``A Read-Only Transaction Anomaly Under Snapshot Isolation", Fekete et al.                 *)
(*     https://www.cs.umb.edu/~poneil/ROAnom.pdf                                                  *)
(*                                                                                                *)
(*     ``Debugging Designs", Chris Newcombe, 2011                                                 *)
(*     https://github.com/pron/amazon-snapshot-spec/blob/master/DebuggingDesigns.pdf              *)
(*                                                                                                *)
(* This spec tries to model things at a very high level of abstraction, so as to communicate the  *)
(* important concepts of snapshot isolation, as opposed to how a system might actually implement  *)
(* it.  Correctness properties and their detailed explanations are included at the end of this    *)
(* spec.  We draw the basic definition of snapshot isolation from Definition 1.1 of Fekete's      *)
(* "Read-Only" anomaly paper:                                                                     *)
(*                                                                                                *)
(*                                                                                                *)
(*     "...we assume time is measured by a counter that advances whenever any                     *)
(* transaction starts or commits, and we designate the time when transaction Ti starts as         *)
(* start(Ti) and the time when Ti commits as commit(Ti).                                          *)
(*                                                                                                *)
(* Definition 1.1: Snapshot Isolation (SI).  A transaction Ti executing under SI conceptually     *)
(* reads data from the committed state of the database as of time start(Ti) (the snapshot), and   *)
(* holds the results of its own writes in local memory store, so if it reads data it has written  *)
(* it will read its own output.  Predicates evaluated by Ti are also based on rows and index      *)
(* entry versions from the committed state of the database at time start(Ti), adjusted to take    *)
(* Ti's own writes into account.  Snapshot Isolation also must obey a "First Committer (Updater)  *)
(* Wins" rule...The interval in time from the start to the commit of a transaction, represented   *)
(* [Start(Ti), Commit(Ti)], is called its transactional lifetime.  We say two transactions T1 and *)
(* T2 are concurrent if their transactional lifetimes overlap, i.e., [start(T1), commit(T1)] ∩    *)
(* [start(T2), commit(T2)] ≠ Φ.  Writes by transactions active after Ti starts, i.e., writes by   *)
(* concurrent transactions, are not visible to Ti.  When Ti is ready to commit, it obeys the      *)
(* First Committer Wins rule, as follows: Ti will successfully commit if and only if no           *)
(* concurrent transaction Tk has already committed writes (updates) of rows or index entries that *)
(* Ti intends to write."                                                                          *)
(*                                                                                                *)
(**************************************************************************************************)


(**************************************************************************************************)
(* The constant parameters of the spec.                                                           *)
(**************************************************************************************************)

\* Set of all transaction ids.
CONSTANT txnIds

\* Set of all data store keys/values.
CONSTANT keys, values

\* An empty value.
CONSTANT Empty

(**************************************************************************************************)
(* The variables of the spec.                                                                     *)
(**************************************************************************************************)

\* The clock, which measures 'time', is just a counter, that increments (ticks) 
\* whenever a transaction starts or commits.
VARIABLE clock

\* The set of all currently running transactions.
VARIABLE runningTxns

\* The full history of all transaction operations. It is modeled as a linear 
\* sequence of events. Such a history would likely never exist in a real implementation, 
\* but it is used in the model to check the properties of snapshot isolation.
VARIABLE txnHistory

\* (NOT NECESSARY)
\* The key-value data store. In this spec, we model a data store explicitly, even though it is not actually
\* used for the verification of any correctness properties. This was added initially as an attempt the make the
\* spec more intuitive and understandable. It may play no important role at this point, however. If a property
\* check was ever added for view serializability, this, and the set of transaction snapshots, may end up being
\* useful.
VARIABLE dataStore

\* (NOT NECESSARY)
\* The set of snapshots needed for all running transactions. Each snapshot 
\* represents the entire state of the data store as of a given point in time. 
\* It is a function from transaction ids to data store snapshots. This, like the 'dataStore' variable, may 
\* now be obsolete for a spec at this level of abstraction, since the correctness properties we check do not 
\* depend on the actual data being read/written.
VARIABLE txnSnapshots

vars == <<clock, runningTxns, txnSnapshots, dataStore, txnHistory>>


(**************************************************************************************************)
(* Data type definitions.                                                                         *)
(**************************************************************************************************)

DataStoreType == [keys -> (values \cup {Empty})]
BeginOpType   == [type : {"begin"}  , txnId : txnIds , time : Nat]
CommitOpType  == [type : {"commit"} , txnId : txnIds , time : Nat, updatedKeys : SUBSET keys]
WriteOpType   == [type : {"write"}  , txnId : txnIds , key: SUBSET keys , val : SUBSET values]
ReadOpType    == [type : {"read"}   , txnId : txnIds , key: SUBSET keys , val : SUBSET values]
AnyOpType     == UNION {BeginOpType, CommitOpType, WriteOpType, ReadOpType}

(**************************************************************************************************)
(* The type invariant and initial predicate.                                                      *)
(**************************************************************************************************)

TypeInvariant == 
    \* /\ txnHistory \in Seq(AnyOpType) seems expensive to check with TLC, so disable it.
    /\ dataStore    \in DataStoreType
    /\ txnSnapshots \in [txnIds -> (DataStoreType \cup {Empty})]
    /\ runningTxns  \in SUBSET [ id : txnIds, 
                                 startTime  : Nat, 
                                 commitTime : Nat \cup {Empty}]

Init ==  
    /\ runningTxns = {} 
    /\ txnHistory = <<>>
    /\ clock = 0
    /\ txnSnapshots = [id \in txnIds |-> Empty]
    /\ dataStore = [k \in keys |-> Empty]

(**************************************************************************************************)
(* Helpers for querying transaction histories.                                                    *)
(*                                                                                                *)
(* These are parameterized on a transaction history and a transaction id, if applicable.          *)
(**************************************************************************************************)

\* Generic TLA+ helper.
Range(f) == {f[x] : x \in DOMAIN f}

\* The begin or commit op for a given transaction id.
BeginOp(h, txnId)  == CHOOSE op \in Range(h) : op.txnId = txnId /\ op.type = "begin"
CommitOp(h, txnId) == CHOOSE op \in Range(h) : op.txnId = txnId /\ op.type = "commit"

\* The set of all committed/aborted transaction ids in a given history.
CommittedTxns(h) == {op.txnId : op \in {op \in Range(h) : op.type = "commit"}}
AbortedTxns(h)   == {op.txnId : op \in {op \in Range(h) : op.type = "abort"}}

\* The set of all read or write ops done by a given transaction.                   
ReadsByTxn(h, txnId)  == {op \in Range(h) : op.txnId = txnId /\ op.type = "read"}
WritesByTxn(h, txnId) == {op \in Range(h) : op.txnId = txnId /\ op.type = "write"}

\* The set of all keys read or written to by a given transaction.                   
KeysReadByTxn(h, txnId)    == { op.key : op \in ReadsByTxn(txnHistory, txnId)}
KeysWrittenByTxn(h, txnId) == { op.key : op \in WritesByTxn(txnHistory, txnId)}

\* The index of a given operation in the transaction history sequence.
IndexOfOp(h, op) == CHOOSE i \in DOMAIN h : h[i] = op

(**************************************************************************************************)
(*                                                                                                *)
(* Action Definitions                                                                             *)
(*                                                                                                *)
(**************************************************************************************************)


(**************************************************************************************************)
(* When a transaction starts, it gets a new, unique transaction id and is added to the set of     *)
(* running transactions.  It also "copies" a local snapshot of the data store on which it will    *)
(* perform its reads and writes against.  In a real system, this data would not be literally      *)
(* "copied", but this is the fundamental concept of snapshot isolation i.e.  that each            *)
(* transaction appears to operate on its own local snapshot of the database.                      *)
(**************************************************************************************************)
StartTxn == \E newTxnId \in txnIds : 
                LET newTxn == 
                    [ id |-> newTxnId, 
                      startTime |-> clock+1, 
                      commitTime |-> Empty] IN
                \* Must choose an unused transaction id. There must be no other operation
                \* in the history that already uses this id.
                /\ ~\E op \in Range(txnHistory) : op.txnId = newTxnId
                \* Save a snapshot of current data store for this transaction, and
                \* and append its 'begin' event to the history.
                /\ txnSnapshots' = [txnSnapshots EXCEPT ![newTxnId] = dataStore]
                /\ LET beginOp == [ type  |-> "begin", 
                                    txnId |-> newTxnId, 
                                    time  |-> clock+1 ] IN
                   txnHistory' = Append(txnHistory, beginOp)
                \* Add transaction to the set of active transactions.
                /\ runningTxns' = runningTxns \cup {newTxn}
                \* Tick the clock.
                /\ clock' = clock + 1    
                /\ UNCHANGED <<dataStore>>
                          
                        
(**************************************************************************************************)
(* When a transaction T0 is ready to commit, it obeys the "First Committer Wins" rule.  T0 will   *)
(* only successfully commit if no concurrent transaction has already committed writes of data     *)
(* objects that T0 intends to write.  Transactions T0, T1 are considered concurrent if the        *)
(* intersection of their timespans is non empty i.e.                                              *)
(*                                                                                                *)
(*     [start(T0), commit(T0)] \cap [start(T1), commit(T1)] != {}                                 *)
(**************************************************************************************************)

\* Checks whether a given transaction is allowed to commit, based on whether it conflicts
\* with other concurrent transactions that have already committed.
TxnCanCommit(txn) == 
    ~\E op \in Range(txnHistory) :
        /\ op.type = "commit" 
        /\ op.time > txn.startTime 
        /\ KeysWrittenByTxn(txnHistory, txn.id) \cap op.updatedKeys /= {} \* Must be no conflicting keys.
         
CommitTxn(txn) == 
    \* Transaction must be able to commit i.e. have no write conflicts with concurrent.
    \* committed transactions.
    /\ TxnCanCommit(txn)  
    /\ LET commitOp == [ type          |-> "commit", 
                         txnId         |-> txn.id, 
                         time          |-> clock + 1,
                         updatedKeys   |-> KeysWrittenByTxn(txnHistory, txn.id)] IN
       txnHistory' = Append(txnHistory, commitOp)            
    \* Merge this transaction's updates into the data store. If the 
    \* transaction has updated a key, then we use its version as the new
    \* value for that key. Otherwise the key remains unchanged.
    /\ dataStore' = [k \in keys |-> IF k \in KeysWrittenByTxn(txnHistory, txn.id) 
                                        THEN txnSnapshots[txn.id][k]
                                        ELSE dataStore[k]]
    \* Remove the transaction from the active set. 
    /\ runningTxns' = runningTxns \ {txn}
    /\ clock' = clock + 1
    \* We can leave the snapshot around, since it won't be used again.
    /\ UNCHANGED <<txnSnapshots>>

(**************************************************************************************************)
(* In this spec, a transaction aborts if and only if it cannot commit, due to write conflicts.    *)
(**************************************************************************************************)
AbortTxn(txn) ==
    \* If a transaction can't commit due to write conflicts, then it
    \* must abort.
    /\ ~TxnCanCommit(txn)
    /\ LET abortOp == [ type   |-> "abort", 
                        txnId  |-> txn.id, 
                        time   |-> clock + 1] IN    
       txnHistory' = Append(txnHistory, abortOp)
    /\ runningTxns' = runningTxns \ {txn} \* transaction is no longer running.
    /\ clock' = clock + 1
    \* No changes are made to the data store.
    /\ UNCHANGED <<dataStore, txnSnapshots>>

\* Ends a given transaction by either committing or aborting it. To exclude uninteresting 
\* histories, we require that a transaction does at least one operation before committing or aborting. 
\* Assumes that the given transaction is currently running.
CompleteTxn(txn) == 
    \* Must not be a no-op transaction.
    /\ (WritesByTxn(txnHistory, txn.id) \cup ReadsByTxn(txnHistory, txn.id)) /= {}
    \* Commit or abort the transaction.
    /\ \/ CommitTxn(txn)
       \/ AbortTxn(txn)

(***************************************************************************************************)
(* Read and write operations executed by transactions.                                            *)
(*                                                                                                *)
(* As a simplification, and to limit the size of potential models, we allow transactions to only  *)
(* read or write to the same key once.  The idea is that it limits the state space without loss   *)
(* of generality.                                                                                 *)
(**************************************************************************************************)

TxnRead(txn, k) == 
    \* Read from this transaction's snapshot.
    LET valRead == txnSnapshots[txn.id][k]
        readOp == [ type  |-> "read", 
                    txnId |-> txn.id, 
                    key   |-> k, 
                    val   |-> valRead] IN
    /\ txnHistory' = Append(txnHistory, readOp)
    /\ UNCHANGED <<dataStore, clock, runningTxns, txnSnapshots>>
                   
TxnUpdate(txn, k, v) == 
    LET writeOp == [ type  |-> "write", 
                     txnId |-> txn.id, 
                     key   |-> k, 
                     val   |-> v] IN    
    \* We update the transaction's snapshot, not the actual data store.
    /\ LET updatedSnapshot == [txnSnapshots[txn.id] EXCEPT ![k] = v] IN
           txnSnapshots' = [txnSnapshots EXCEPT ![txn.id] = updatedSnapshot]
    /\ txnHistory' = Append(txnHistory, writeOp)
    /\ UNCHANGED <<dataStore, runningTxns, clock>>

\* A read or write action by a running transaction. We limit transactions
\* to only read or write the same key once.
TxnReadWrite(txn) == 
       \E k \in keys : 
       \E v \in values :
            \/ TxnRead(txn, k) /\ k \notin KeysReadByTxn(txnHistory, txn.id)
            \/ TxnUpdate(txn, k, v) /\ k \notin KeysWrittenByTxn(txnHistory, txn.id)
            
            
(**************************************************************************************************)
(* The next-state relation and spec definition.                                                   *)
(*                                                                                                *)
(* Since it is desirable to have TLC check for deadlock, which may indicate bugs in the spec or   *)
(* in the algorithm, we want to explicitly define what a "valid" termination state is.  If all    *)
(* transactions have run and either committed or aborted, we consider that valid termination, and *)
(* is allowed as an infinite suttering step.                                                      *)
(*                                                                                                *)
(* Also, once a transaction knows that it cannot commit due to write conflicts, we don't let it   *)
(* do any more reads or writes, so as to eliminate wasted operations.  That is, once we know a    *)
(* transaction can't commit, we force its next action to be abort.                                *)
(**************************************************************************************************)           

AllTxnsFinished == AbortedTxns(txnHistory) \cup CommittedTxns(txnHistory) = txnIds
    
Next == \/ StartTxn 
        \/ \E txn \in runningTxns : 
                \/ CompleteTxn(txn)
                \/ TxnReadWrite(txn) /\ TxnCanCommit(txn)
        \/ (AllTxnsFinished /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)


----------------------------------------------------------------------------------------------------


(**************************************************************************************************)
(*                                                                                                *)
(* Correctness Properties and Tests                                                               *)
(*                                                                                                *)
(**************************************************************************************************)



(**************************************************************************************************)
(* Operator for computing cycles in a given graph, defined by a set of edges.                     *)
(*                                                                                                *)
(* Returns a set containing all elements that participate in any cycle (i.e.  union of all        *)
(* cycles), or an empty set if no cycle is found.                                                 *)
(*                                                                                                *)
(* Source:                                                                                        *)
(* https://github.com/pron/amazon-snapshot-spec/blob/master/serializableSnapshotIsolation.tla.    *)
(**************************************************************************************************)
\* FindAllNodesInAnyCycle(edges) ==

\*     LET RECURSIVE findCycleNodes(_, _)   (* startNode, visitedSet *)
\*         (* Returns a set containing all elements of some cycle starting at startNode,
\*            or an empty set if no cycle is found. 
\*          *)
\*         findCycleNodes(node, visitedSet) ==
\*             IF node \in visitedSet THEN
\*                 {node}  (* found a cycle, which includes node *)
\*             ELSE
\*                 LET newVisited == visitedSet \union {node}
\*                     neighbors == {to : <<from, to>> \in 
\*                                            {<<from, to>> \in edges : from = node}}
\*                 IN  (* Explore neighbors *)
\*                     UNION {findCycleNodes(neighbor, newVisited) : neighbor \in neighbors}
                    
\*         startPoints == {from : <<from, to>> \in edges}  (* All nodes with an outgoing edge *)
\*     IN 
\*         UNION {findCycleNodes(node, {}) : node \in startPoints}
       
\* IsCycle(edges) == FindAllNodesInAnyCycle(edges) /= {}



(**************************************************************************************************)
(*                                                                                                *)
(* Verifying Serializability                                                                      *)
(*                                                                                                *)
(* ---------------------------------------                                                        *)
(*                                                                                                *)
(* For checking serializability of transaction histories we use the "Conflict Serializability"    *)
(* definition.  This is slightly different than what is known as "View Serializability", but is   *)
(* suitable for verification, since it is efficient to check, whereas checking view               *)
(* serializability of a transaction schedule is known to be NP-complete.                          *)
(*                                                                                                *)
(* The definition of conflict serializability permits a more limited set of transaction           *)
(* histories.  Intuitively, it can be viewed as checking whether a given schedule has the         *)
(* "potential" to produce a certain anomaly, even if the particular data values for a history     *)
(* make it serializable.  Formally, we can think of the set of conflict serializable histories as *)
(* a subset of all possible serializable histories.  Alternatively, we can say that, for a given  *)
(* history H ConflictSerializable(H) => ViewSerializable(H).  The converse, however, is not true. *)
(* A history may be view serializable but not conflict serializable.                              *)
(*                                                                                                *)
(* In order to check for conflict serializability, we construct a multi-version serialization     *)
(* graph (MVSG).  Details on MVSG can be found, among other places, in Cahill's thesis, Section   *)
(* 2.5.1.  To construct the MVSG, we put an edge from one committed transaction T1 to another     *)
(* committed transaction T2 in the following situations:                                          *)
(*                                                                                                *)
(*   (WW-Dependency)                                                                              *)
(*   T1 produces a version of x, and T2 produces a later version of x.                            *)
(*                                                                                                *)
(*   (WR-Dependency)                                                                              *)
(*   T1 produces a version of x, and T2 reads this (or a later) version of x.                     *)
(*                                                                                                *)
(*   (RW-Dependency)                                                                              *)
(*   T1 reads a version of x, and T2 produces a later version of x. This is                       *)
(*   the only case where T1 and T2 can run concurrently.                                          *)
(*                                                                                                *)
(**************************************************************************************************)

\* T1 wrote to a key that T2 then also wrote to. The First Committer Wins rule implies
\* that T1 must have committed before T2 began.
WWDependency(h, t1Id, t2Id) == 
    \E op1 \in WritesByTxn(h, t1Id) :
    \E op2 \in WritesByTxn(h, t2Id) :
        /\ op1.key = op2.key
        /\ CommitOp(h, t1Id).time < CommitOp(h, t2Id).time

\* T1 wrote to a key that T2 then later read, after T1 committed.
WRDependency(h, t1Id, t2Id) == 
    \E op1 \in WritesByTxn(h, t1Id) :
    \E op2 \in ReadsByTxn(h, t2Id) :
        /\ op1.key = op2.key
        /\ CommitOp(h, t1Id).time < BeginOp(h, t2Id).time   

\* T1 read a key that T2 then later wrote to. T1 must start before T2 commits, since this implies that T1 read  
\* a version of the key and T2 produced a later version of that ke, i.e. when it commits. T1, however, read 
\* an earlier version of that key, because it started before T2 committed.
RWDependency(h, t1Id, t2Id) == 
    \E op1 \in ReadsByTxn(h, t1Id) :
    \E op2 \in WritesByTxn(h, t2Id) :
        /\ op1.key = op2.key
        /\ BeginOp(h, t1Id).time < CommitOp(h, t2Id).time  \* T1 starts before T2 commits. This means that T1 read
        

\* Produces the serialization graph as defined above, for a given history. This graph is produced 
\* by defining the appropriate set comprehension, where the produced set contains all the edges of the graph.
SerializationGraph(history) == 
    LET committedTxnIds == CommittedTxns(history) IN
    {<<t1, t2>> \in (committedTxnIds \X committedTxnIds):
        /\ t1 /= t2
        /\ \/ WWDependency(history, t1, t2)
           \/ WRDependency(history, t1, t2)
           \/ RWDependency(history, t1, t2)}

\* The key property to verify i.e. serializability of transaction histories.
\* IsConflictSerializable(h) == ~IsCycle(SerializationGraph(h))

\* Examples of each dependency type.
HistWW == << [type |-> "begin"  , txnId |-> 0 , time |-> 0],
             [type |-> "write"  , txnId |-> 0 , key  |-> "k1" , val |-> "v1"],
             [type |-> "commit" , txnId |-> 0 , time |-> 1, updatedKeys |-> {"k1"}],
             [type |-> "begin"  , txnId |-> 1 , time |-> 2],
             [type |-> "write"  , txnId |-> 1 , key  |-> "k1" , val |-> "v1"],
             [type |-> "commit" , txnId |-> 1 , time |-> 3, updatedKeys |-> {"k1"}]>>

HistWR == << [type |-> "begin"  , txnId |-> 0 , time |-> 0],
             [type |-> "write"  , txnId |-> 0 , key  |-> "k1" , val |-> "v1"],
             [type |-> "commit" , txnId |-> 0 , time |-> 1, updatedKeys |-> {"k1"}],
             [type |-> "begin"  , txnId |-> 1 , time |-> 2],
             [type |-> "read"   , txnId |-> 1 , key  |-> "k1" , val |-> "v1"],
             [type |-> "commit" , txnId |-> 1 , time |-> 3, updatedKeys |-> {}]>>

HistRW == << [type |-> "begin"  , txnId |-> 0 , time |-> 0],
             [type |-> "read"   , txnId |-> 0 , key  |-> "k1" , val |-> "empty"],
             [type |-> "begin"  , txnId |-> 1 , time |-> 1],
             [type |-> "write"   , txnId |-> 1 , key  |-> "k1" , val |-> "v1"],
             [type |-> "commit" , txnId |-> 1 , time |-> 2, updatedKeys |-> {}],
             [type |-> "commit" , txnId |-> 0 , time |-> 3, updatedKeys |-> {"k1"}]>>

\* A simple invariant to test the correctness of dependency definitions.
WWDependencyCorrect == WWDependency(HistWW, 0, 1)
WRDependencyCorrect == WRDependency(HistWR, 0, 1)
RWDependencyCorrect == RWDependency(HistRW, 0, 1)
MVSGDependencyCorrect == WWDependencyCorrect /\ WRDependencyCorrect /\ RWDependencyCorrect
   
     
(**************************************************************************************************)
(* Examples of concurrency phenomena under Snapshot Isolation.  These are for demonstration       *)
(* purposes and can be used for checking the above definitions of serializability.                *)
(*                                                                                                *)
(* Write Skew:                                                                                    *)
(*                                                                                                *)
(* Example history from Michael Cahill's Phd thesis:                                              *)
(*                                                                                                *)
(* Section 2.5.1, pg.  16                                                                         *)
(* https://ses.library.usyd.edu.au/bitstream/2123/5353/1/michael-cahill-2009-thesis.pdf           *)
(*                                                                                                *)
(* H: r1(x=50) r1(y=50) r2(x=50) r2(y=50) w1(x=-20) w2(y=-30) c1 c2                               *)
(*                                                                                                *)
(*                                                                                                *)
(* Read-Only Anomaly:                                                                             *)
(*                                                                                                *)
(* "A Read-Only Transaction Anomaly Under Snapshot Isolation", Fekete, O'Neil, O'Neil             *)
(* https://www.cs.umb.edu/~poneil/ROAnom.pdf                                                      *)
(*                                                                                                *)
(*                                                                                                *)
(**************************************************************************************************)

WriteSkewAnomalyTest == <<
    [type |-> "begin",  txnId |-> 1, time |-> 1],                       
    [type |-> "begin",  txnId |-> 2, time |-> 2],
    [type |-> "read",   txnId |-> 1, key |-> "X", val |-> "Empty"],                      
    [type |-> "read",   txnId |-> 1, key |-> "Y", val |-> "Empty"],                      
    [type |-> "read",   txnId |-> 2, key |-> "X", val |-> "Empty"],                      
    [type |-> "read",   txnId |-> 2, key |-> "Y", val |-> "Empty"],                    
    [type |-> "write",  txnId |-> 1, key |-> "X", val |-> 30],           
    [type |-> "write",  txnId |-> 2, key |-> "Y", val |-> 20],        
    [type |-> "commit", txnId |-> 1, time |-> 3, updatedKeys |-> {"X"}],
    [type |-> "commit", txnId |-> 2, time |-> 4, updatedKeys |-> {"Y"}]>>

ReadOnlyAnomalyTest == <<
    [type |-> "begin",  txnId |-> 0, time |-> 0], 
    [type |-> "write",  txnId |-> 0, key |-> "K_X", val |-> 0], 
    [type |-> "write",  txnId |-> 0, key |-> "K_Y", val |-> 0], 
    [type |-> "commit", txnId |-> 0, time |-> 1, updatedKeys |-> {"K_X", "K_Y"}],
    
    (* the history from the paper *) 
                     [type |-> "begin",  txnId |-> 2, time |-> 2], 
    (* R2(X0,0)   *) [type |-> "read",   txnId |-> 2, key |-> "K_X", ver |-> "T_0"], 
    (* R2(Y0,0)   *) [type |-> "read",   txnId |-> 2, key |-> "K_Y", ver |-> "T_0"],
                      
                     [type |-> "begin",  txnId |-> 1, time |-> 3], 
    (* R1(Y0,0)   *) [type |-> "read",   txnId |-> 1, key |-> "K_Y"], 
    (* W1(Y1,20)  *) [type |-> "write",  txnId |-> 1, key |-> "K_Y", val |-> 20],
    (* C1         *) [type |-> "commit", txnId |-> 1, time |-> 4, updatedKeys |-> {"K_Y"}],
     
                     [type |-> "begin",  txnId |-> 3, time |-> 5], 
    (* R3(X0,0)   *) [type |-> "read",   txnId |-> 3, key |-> "K_X", ver |-> "T_0"], 
    (* R3(Y1,20)  *) [type |-> "read",   txnId |-> 3, key |-> "K_Y", ver |-> "T_1"], 
    (* C3         *) [type |-> "commit", txnId |-> 3, time |-> 6, updatedKeys |-> {}],
                      
    (* W2(X2,-11) *) [type |-> "write",  txnId |-> 2, key |-> "K_X", val |-> (0 - 11)], 
    (* C2         *) [type |-> "commit", txnId |-> 2, time |-> 7, updatedKeys |-> {"K_X"}]
    >>

(**************************************************************************************************)
(* Checks if a given history contains a "read-only" anomaly.  In other words, is this a           *)
(* non-serializable transaction history such that it contains a read-only transaction T, and      *)
(* removing T from the history makes the history serializable.                                    *)
(**************************************************************************************************)

\* ReadOnlyAnomaly(h) == 
\*     /\ ~IsConflictSerializable(h)
\*     /\ \E txnId \in CommittedTxns(h) :
\*         \* Transaction only did reads.
\*         /\ WritesByTxn(h, txnId) = {}
\*         \* Removing the transaction makes the history serializable
\*         /\ LET txnOpsFilter(t) == (t.txnId # txnId)
\*            hWithoutTxn == SelectSeq(h, txnOpsFilter) IN
\*            IsConflictSerializable(hWithoutTxn)


---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------



\* (**************************************************************************************************)
\* (* View Serializability (Experimental).                                                           *)
\* (*                                                                                                *)
\* (* A transaction history is view serializable if the reads and writes of all transaction          *)
\* (* oeprations are equivalent the reads and writes of some serial schedule.  View serializability  *)
\* (* encodes a more intuitive notion of serializability i.e.  the overall effect of a sequence of   *)
\* (* interleaved transactions is the same as if it they were executed in sequential order.          *)
\* (**************************************************************************************************)

\* Maximum(S) == CHOOSE x \in S : \A y \in S : y <= x

\* \* The set of all permutations of elements of a set S whose length are the cardinality of S.
\* SeqPermutations(S) == LET D == 1..Cardinality(S) IN {f \in [D -> S] : \A w \in S : \E v \in D : f[v]=w}

\* \* Flattens a sequence of sequences.
\* RECURSIVE Flatten(_)
\* Flatten(seq) == IF Len(seq) = 0 THEN <<>> ELSE Head(seq) \o Flatten(Tail(seq))

\* \* The subsequence of all operations executed by a given transaction id in a history. The original ordering 
\* \* of the operations is maintained.
\* OpsForTxn(h, txnId) == SelectSeq(h, LAMBDA t : t.txnId = txnId)
\* SerialHistories(h) == 
\*     LET serialOrderings == SeqPermutations({ OpsForTxn(h, tid) : tid \in CommittedTxns(h) }) IN
\*     {Flatten(o) : o \in serialOrderings}

\* \* We "execute" a given serial history. To do this, we really only need to determine what the new values of the 
\* \* 'read' operations are, since writes are not changed. To do this, we simply replace the value of each read operation
\* \* in the history with the appropriate one.
\* ExecuteSerialHistory(h) ==
\*     [i \in DOMAIN h |-> 
\*         IF h[i].type = "read" 
\*             \* We need to determine what value to read for this operation; we use the
\*             \* the value of the last write to this key.
\*             THEN LET prevWriteOpInds == {ind \in DOMAIN h : 
\*                                                 /\  ind < i 
\*                                                 /\  h[ind].type = "write"
\*                                                 /\  h[ind].key = h[i].key} IN
\*                      IF prevWriteOpInds = {} 
\*                         THEN [h[i] EXCEPT !.val = Empty]
\*                         ELSE LET latestWriteOpToKey == h[Maximum(prevWriteOpInds)] IN
\*                              [h[i] EXCEPT !.val = latestWriteOpToKey.val] 
\*             ELSE h[i]]

\* IsViewEquivalent(h1, h2) == 
\*     \A tid \in CommittedTxns(h1) : OpsForTxn(h1, tid) = OpsForTxn(h2, tid)

\* ViewEquivalentHistory(h) == {ExecuteSerialHistory(serial) : serial \in 
\*                                 {h2 \in SerialHistories(h) : IsViewEquivalent(h, ExecuteSerialHistory(h2))}}

\* IsViewSerializable(h) == \E h2 \in SerialHistories(h) : IsViewEquivalent(h, ExecuteSerialHistory(h2))


=============================================================================
\* Modification History
\* Last modified Tue Feb 27 12:56:09 EST 2018 by williamschultz
\* Created Sat Jan 13 08:59:10 EST 2018 by williamschultz