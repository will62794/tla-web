\* Copyright 2024 MongoDB, Inc.
\*
\* This work is licensed under:
\* - Creative Commons Attribution-3.0 United States License
\*   http://creativecommons.org/licenses/by/3.0/us/

------------------------------------- MODULE TxnsMoveRange -----------------------------------------
\* This is the formal specification for the multi-statement transactions data consistency
\* protocol, with sub-snapshot read concern level and in the presence of range migrations.
\* It covers the placement versioning protocol, and the `placementConflictTime' protocol that
\* forbids the data placement anomaly described at:
\* https://github.com/mongodb/mongo/blob/master/src/mongo/db/s/README_transactions_and_ddl.md
\*
\* To run the model-checker, first edit the constants in MCTxnsMoveRange.cfg if desired, then:
\*     cd src/mongo/tla_plus
\*     ./model-check.sh TxnsMoveRange

EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS
    Shards,
    Keys,
    NameSpaces,
    Txns,
    MIGRATIONS,
    TXN_STMTS

    STL  == "staleRouter"
    SIN  == "snapIncompatible"
    OK   == "ok"

ASSUME Cardinality(Shards) > 1
ASSUME Cardinality(Keys) > 0
ASSUME Cardinality(NameSpaces) > 0
ASSUME Cardinality(Txns) > 0
ASSUME MIGRATIONS \in 0..100
ASSUME TXN_STMTS \in 1..100

INIT_MIGRATION_TS == 100
MIGRATION_TS_DOMAIN == INIT_MIGRATION_TS..INIT_MIGRATION_TS+MIGRATIONS
Stmts == 1..TXN_STMTS
Status == {STL, SIN, OK}

\* A router request.
\* 's' is the target shard. 'ns' is the target namespace. 'k' is the query predicate (a key match).
\* 'v' is the placement version. 'cts' is the placementConflictTimestamp.
ReqEntry == [s: Shards, ns: NameSpaces, k: Keys, v: 0..MIGRATIONS, cts: MIGRATION_TS_DOMAIN]
CreateReq(s, ns, k, v, cts) == [s |->s, ns |-> ns, k |-> k, v |-> v, cts |-> cts]
\* A shard's response to a router request. 'found' indicates whether the key matched in the shard.
RspEntry == [rsp: {STL, SIN, OK}, found: {TRUE, FALSE}]
CreateRsp(rsp, found) == [rsp |-> rsp, found |-> found]
HasResponse(stmt) == Cardinality(DOMAIN stmt) # 0

RespondStatus(receivedPlacementV, shardLastPlacementV, placementConflictTs, shardLastMigrationTs) ==
    IF receivedPlacementV < shardLastPlacementV THEN STL
        ELSE IF placementConflictTs < shardLastMigrationTs THEN SIN
            ELSE OK

Max(S) == CHOOSE x \in S : \A y \in S : x >= y

VARIABLES ranges, versions, request, response, locked \* global vars
VARIABLES cachedVersions, cachedRanges, pConflictTs, completedStmt \* router vars
VARIABLES lastMigrationTs, snapshotted, snapshot, migrations \* shard vars
vars == <<ranges, versions, request, response, locked, cachedVersions, cachedRanges, pConflictTs,
          completedStmt, lastMigrationTs, snapshotted, snapshot, migrations>>
router_vars == <<cachedRanges, cachedVersions, pConflictTs, completedStmt, request>>
shard_vars == <<snapshotted, snapshot, response>>
migration_vars== <<lastMigrationTs, ranges, versions, migrations>>

Init == (* Global *)
        /\ ranges \in [NameSpaces -> [Keys -> Shards]]
        /\ versions = [s \in Shards |-> [n \in NameSpaces |-> 0]]
        /\ request = [t \in Txns |-> <<>>]
        /\ response = [t \in Txns |-> [stm \in Stmts |-> <<>>]]
        (* Router *)
        /\ cachedVersions = [n \in NameSpaces |-> [s \in Shards |-> 0]]
        /\ cachedRanges = [n \in NameSpaces |-> ranges[n]]
        /\ pConflictTs = [t \in Txns |-> -1] \* placementConflictTs the router chooses for a txn
        /\ completedStmt = [t \in Txns |-> 0]
        (* Shard *)
        /\ snapshotted = [self \in Shards |-> [t \in Txns |-> FALSE]]
        /\ snapshot = [self \in Shards |-> [t \in Txns |-> [n \in NameSpaces |-> {}]]]
        /\ lastMigrationTs = [s \in Shards |-> [n \in NameSpaces |-> INIT_MIGRATION_TS]]
        /\ locked = [s \in Shards |-> [t \in Txns |-> [n \in NameSpaces |-> FALSE]]]
        /\ migrations = 0

LatestMigrationTs == Max(UNION {{lastMigrationTs[n][x] :
                                    x \in DOMAIN lastMigrationTs[n]} :
                                        n \in DOMAIN lastMigrationTs})
TxnCommitted(t) == HasResponse(response[t][TXN_STMTS]) /\ response[t][TXN_STMTS]["rsp"] = OK
TxnAborted(t) == \E s \in Stmts : HasResponse(response[t][s]) /\ response[t][s]["rsp"] \notin {OK}
Done == \A t \in Txns : completedStmt[t] = TXN_STMTS
IsNamespaceLocked(s, ns) == \E t \in Txns : locked[s][t][ns]
Lock(lk, t, s, ns) == [lk EXCEPT ![s][t][ns] = TRUE]
Unlock(t) == [s \in Shards |->
                [txn \in Txns |->
                    [ns \in NameSpaces |-> IF txn = t THEN FALSE ELSE locked[s][txn][ns]]]]

\* Action: the router forwards a transaction statement to the shard owning the key.
RouterSendTxnStmt(t, ns, k) ==
    /\ ~Done
    /\ Len(request[t]) < TXN_STMTS
    /\ completedStmt[t]=Len(request[t])
    /\ IF pConflictTs[t] = -1
        THEN pConflictTs' = [pConflictTs  EXCEPT ![t] = LatestMigrationTs]
        ELSE UNCHANGED pConflictTs
    /\ LET s == cachedRanges[ns][k] IN
        /\ request' = [request EXCEPT ![t] = Append(request[t], CreateReq(s, ns, k,
                                                                          cachedVersions[ns][s],
                                                                          pConflictTs'[t]))]
    /\ UNCHANGED <<shard_vars, migration_vars, completedStmt, locked, cachedRanges, cachedVersions>>

\* Action: router processes a non-OK response from a shard.
RouterHandleAbort(t, stm) ==
    /\ ~Done
    /\ HasResponse(response[t][stm])
    /\ completedStmt[t]<stm
    /\ response[t][stm]["rsp"] \notin {OK}
    /\ IF response[t][stm]["rsp"] = STL
        THEN
            /\ LET ns == request[t][Len(request[t])]["ns"] IN
                /\ cachedVersions' =
                    [cachedVersions EXCEPT ![ns] = [x \in Shards |-> versions[x][ns]]]
                /\ cachedRanges' = [cachedRanges EXCEPT ![ns] = ranges[ns]]
        ELSE UNCHANGED <<cachedVersions, cachedRanges>>
    /\ completedStmt' = [completedStmt EXCEPT ![t] = TXN_STMTS]
    /\ locked' = Unlock(t) \* Avoid a ShardAbortTxn action which would increase the state space.
    /\ UNCHANGED <<shard_vars, migration_vars, request, pConflictTs>>

\* Action: router processes an OK response from a shard.
RouterHandleOK(t, stm) ==
    /\ ~Done
    /\ HasResponse(response[t][stm])
    /\ completedStmt[t]<stm
    /\ response[t][stm]["rsp"] \notin  {STL, SIN}
    /\ completedStmt' = [completedStmt EXCEPT ![t] = completedStmt[t]+1]
    \* Avoid a ShardCommitTxn action which would increase the state space.
    /\ IF completedStmt'[t] = TXN_STMTS THEN locked' = Unlock(t) ELSE UNCHANGED locked
    /\ UNCHANGED <<shard_vars, migration_vars, request, cachedVersions, cachedRanges, pConflictTs>>

\* Action: shard responds to a statement forwarded by the router.
ShardRespond(t, self) ==
    /\ ~Done
    /\ Len(request[t]) > 0 \* added explicit check for length bound validity
    /\ LET  ln == Len(request[t])
            req == request[t][ln] IN
        /\ ln > 0
        /\ req.s = self
        /\ response[t][ln] = <<>>
        /\ IF snapshotted[self][t] = FALSE THEN
                /\ snapshotted' = [snapshotted EXCEPT ![self][t] = TRUE]
                /\ snapshot' = [snapshot EXCEPT ![self][t] =
                    [n \in NameSpaces |-> {k \in DOMAIN(ranges[n]) : ranges[n][k] = self}]]
            ELSE
                /\ UNCHANGED <<snapshot, snapshotted>>
        /\ response' = [response EXCEPT ![t][ln] =
                            CreateRsp(RespondStatus(req.v, versions[self][req.ns], req.cts,
                                                    lastMigrationTs[self][req.ns]),
                                                    req.k \in snapshot'[self][t][req.ns])]
        /\ locked' = Lock(locked, t, req.s, req.ns)
    /\ UNCHANGED <<router_vars, migration_vars>>

\* Action: shard migrates one of its keys to another shard.
MoveRange(ns, k) ==
    /\ migrations < MIGRATIONS
    /\ LET from == ranges[ns][k]
           to == CHOOSE s \in Shards : s # from
           v == Max({versions[s][ns]: s \in Shards}) IN
        /\ ~IsNamespaceLocked(from, ns)
        /\ ~IsNamespaceLocked(to, ns)
        /\ versions' = [versions EXCEPT ![from][ns] = v + 1,
                                        ![to][ns] = v + 1]
        /\ ranges' = [ranges EXCEPT ![ns][k] = to]
        \* Only update the "last migration" timestamp on the recipient shard.
        /\ lastMigrationTs' = [lastMigrationTs EXCEPT ![to][ns] = LatestMigrationTs + 1]
    /\ migrations' = migrations+1
    /\ UNCHANGED <<router_vars, shard_vars, locked>>

Next ==
    \* Router actions
    \/ \E t \in Txns, ns \in NameSpaces, k \in Keys: RouterSendTxnStmt(t, ns, k)
    \/ \E t \in Txns, stm \in Stmts: RouterHandleAbort(t, stm)
    \/ \E t \in Txns, stm \in Stmts: RouterHandleOK(t, stm)
    \* Placer actions
    \/ \E ns \in NameSpaces, k \in Keys : MoveRange(ns, k)
    \* Shard actions
    \/ \E s \in Shards, t \in Txns: ShardRespond(t, s)
    \* Termination
    \/ (Done /\ UNCHANGED vars)

Fairness == TRUE
    /\ WF_vars(\E t \in Txns, ns \in NameSpaces, k \in Keys : RouterSendTxnStmt(t, ns, k))
    /\ WF_vars(\E t \in Txns, stm \in Stmts: RouterHandleAbort(t, stm))
    /\ WF_vars(\E t \in Txns, stm \in Stmts: RouterHandleOK(t, stm))
    /\ WF_vars(\E ns \in NameSpaces, k \in Keys : MoveRange(ns, k))
    /\ WF_vars(\E s \in Shards, t \in Txns: ShardRespond(t, s))

Spec == /\ Init /\ [][Next]_vars /\ Fairness

Termination == <>Done 

----------------------------------------------------------------------------------------------------

(**************************************************************************************************)
(* Type invariants.                                                                               *)
(**************************************************************************************************)
TypeOK ==
    /\ request \in [Txns -> Seq(ReqEntry)]
    /\ ranges \in [NameSpaces -> [Keys -> Shards]]
    /\ versions \in [Shards -> [NameSpaces -> 0..MIGRATIONS]]
    /\ cachedVersions \in [NameSpaces -> [Shards -> -1..MIGRATIONS]]
    /\ lastMigrationTs \in [Shards -> [NameSpaces -> MIGRATION_TS_DOMAIN]]

(**************************************************************************************************)
(* Miscellaneous properties for exploring/understanding the spec.                                 *)
(**************************************************************************************************)

\* Namespaces involved in a transaction
NSsetofTxn(t) == { request[t][x].ns : x \in 1..Len(request[t]) }

\* Shards involved in a transaction
ShardsetofTxn(t) == { request[t][x].s : x \in 1..Len(request[t]) }

\* shard-ns tuples in a transaction
SNStuplesetofTxn(t) == { <<request[t][x].s, request[t][x].ns>> : x \in 1..Len(request[t]) }

(**************************************************************************************************)
(* Correctness Properties                                                                         *)
(**************************************************************************************************)

CommittedTxnImpliesAllStmtsSuccessful ==
    \A t \in Txns: TxnCommitted(t) => \A s \in Stmts : response[t][s]["rsp"] = OK
CommittedTxnImpliesKeysAreVisible ==
    \A t \in Txns: TxnCommitted(t) => \A s \in Stmts : response[t][s]["found"] = TRUE

AllTxnsEventuallyDone == <> \A t \in Txns : TxnCommitted(t) \/ TxnAborted(t)
AllLocksEventuallyRescinded ==
    <>(locked = [s \in Shards |-> [t \in Txns |-> [n \in NameSpaces |-> FALSE]]])

(**************************************************************************************************)
(* Counterexamples.                                                                               *)
(**************************************************************************************************)

\* Produces a snapshotIncompatible counterexample.
BaitSIN ==
    ~(\E t \in Txns, stm \in Stmts: HasResponse(response[t][stm]) /\ response[t][stm]["rsp"]=SIN)

\* Produces a counterexample trace where all transactions commit.
BaitHappyPath ==
    <>(\E t \in Txns, stm \in Stmts:
            HasResponse(response[t][stm]) /\ response[t][stm]["rsp"] \in {SIN, STL})

\* Produces a counterexample trace of length >=N.
BaitTrace ==
    TLCGet("level") < 155

====================================================================================================