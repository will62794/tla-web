---- MODULE MongoRaftReconfig ----
\*
\* High level specification of Raft protocol with dynamic reconfiguration.
\*

EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC


CONSTANTS Server

CONSTANTS Secondary, Primary, Nil

CONSTANT InitTerm

VARIABLE currentTerm
VARIABLE state
VARIABLE log
VARIABLE immediatelyCommitted

\* Configuration related variables.
VARIABLE config
VARIABLE configVersion
VARIABLE configTerm

vars == <<currentTerm, state, log, immediatelyCommitted, configVersion, configTerm, config>>

\* The set of all allowed config sets.
AllConfigs == SUBSET Server

\*
\* Helper operators.
\*

\* Is a sequence empty.
Empty(s) == Len(s) = 0

\* Is log entry e = <<index, term>> in the log of node 'i'.
\* @type: (<<Int,Int>>,SERVER) => Bool;
InLog(e, i) == \E x \in DOMAIN log[i] : x = e[1] /\ log[i][x] = e[2]

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]

\* @type: Seq(Int) => <<Int, Int>>;
LastEntry(xlog) == <<Len(xlog),xlog[Len(xlog)]>>

\* @type: (Seq(Int), Int) => Int;
GetTerm(xlog, index) == IF index = 0 THEN 0 ELSE xlog[index]
LogTerm(i, index) == GetTerm(log[i], index)

\* The set of all quorums in a given set.
Quorums(S) == {i \in SUBSET(S) : Cardinality(i) * 2 > Cardinality(S)}

\* Do all quorums of two sets intersect.
QuorumsOverlap(x, y) == \A qx \in Quorums(x), qy \in Quorums(y) : qx \cap qy # {}

\* The min/max of a set of numbers.
\* Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Max(s) == CHOOSE x \in s : \A y \in s : x >= y

\* Is it possible for log 'i' to roll back against log 'j'. 
\* If this is true, it implies that log 'i' should remove entries from the end of its log.
CanRollback(i, j) ==
    /\ Len(log[i]) > 0
    /\ \* The log with later term is more up-to-date.
       LastTerm(log[i]) < LastTerm(log[j])
    /\ \/ Len(log[i]) > Len(log[j])
       \* There seems no short-cut of OR clauses, so we specify the negative case.
       \/ /\ Len(log[i]) <= Len(log[j])
          /\ LastTerm(log[i]) /= LogTerm(j, Len(log[i]))

\* Can node 'i' currently cast a vote for node 'j' in term 'term'.
CanVoteForOplog(i, j, term) ==
    LET logOk ==
        \/ LastTerm(log[j]) > LastTerm(log[i])
        \/ /\ LastTerm(log[j]) = LastTerm(log[i])
           /\ Len(log[j]) >= Len(log[i]) IN
    /\ currentTerm[i] < term
    /\ logOk

\* Is a log entry 'e'=<<i, t>> immediately immediatelyCommitted in term 't' with a quorum 'Q'.
\* @type: (<<Int, Int>>, Set(SERVER)) => Bool;
ImmediatelyCommitted(e, Q) == 
    LET eind == e[1] 
        eterm == e[2] IN
    \A s \in Q :
        /\ Len(log[s]) >= eind
        /\ InLog(e, s) \* they have the entry.
        /\ currentTerm[s] = eterm  \* they are in the same term as the log entry. 

\* Helper operator for actions that propagate the term between two nodes.
UpdateTermsExpr(i, j) ==
    /\ currentTerm[i] > currentTerm[j]
    /\ currentTerm' = [currentTerm EXCEPT ![j] = currentTerm[i]]
    /\ state' = [state EXCEPT ![j] = Secondary] 


\* (configVersion, term) pair of node i.
CV(i) == <<configVersion[i], configTerm[i]>>

\* Is the config of node i considered 'newer' than the config of node j. This is the condition for
\* node j to accept the config of node i.
IsNewerConfig(i, j) ==
    \/ configTerm[i] > configTerm[j]
    \/ /\ configTerm[i] = configTerm[j]
       /\ configVersion[i] > configVersion[j]

IsNewerOrEqualConfig(i, j) ==
    \/ /\ configTerm[i] = configTerm[j]
       /\ configVersion[i] = configVersion[j]
    \/ IsNewerConfig(i, j)

\* Compares two configs given as <<configVersion, configTerm>> tuples.
NewerConfig(ci, cj) ==
    \* Compare configTerm first.
    \/ ci[2] > cj[2] 
    \* Compare configVersion if terms are equal.
    \/ /\ ci[2] = cj[2]
       /\ ci[1] > cj[1]  

\* Compares two configs given as <<configVersion, configTerm>> tuples.
NewerOrEqualConfig(ci, cj) == NewerConfig(ci, cj) \/ ci = cj

\* Can node 'i' currently cast a vote for node 'j' in term 'term'.
CanVoteForConfig(i, j, term) ==
    /\ currentTerm[i] < term
    /\ IsNewerOrEqualConfig(j, i)
    
\* A quorum of servers in the config of server i have i's config.
ConfigQuorumCheck(i) ==
    \E Q \in Quorums(config[i]) : \A t \in Q : 
        /\ configVersion[t] = configVersion[i]
        /\ configTerm[t] = configTerm[i]

\* A quorum of servers in the config of server i have the term of i.
TermQuorumCheck(i) ==
    \E Q \in Quorums(config[i]) : \A t \in Q : currentTerm[t] = currentTerm[i]    

\* Check whether the entry at "index" on "primary" is immediatelyCommitted in the primary's current config.
IsCommitted(index, primary) ==
    \* The primary must contain such an entry.
    /\ Len(log[primary]) >= index
    \* The entry was written by this leader.
    /\ LogTerm(primary, index) = currentTerm[primary]
    /\ \E quorum \in Quorums(config[primary]):
        \* all nodes have this log entry and are in the term of the leader.
        \A s \in quorum : \E k \in DOMAIN log[s] :
            /\ k = index
            /\ log[s][k] = log[primary][k]    \* they have the entry.
            /\ currentTerm[s] = currentTerm[primary]  \* they are in the same term.

\*
\* This is the precondition about immediatelyCommitted oplog entries that must be satisfied
\* on a primary server s in order for it to execute a reconfiguration.
\*
\* When a primary is first elected in term T, we can be sure that it contains
\* all immediatelyCommitted entries from terms < T. During its reign as primary in term T
\* though, it needs to make sure that any entries it commits in its own term are
\* correctly transferred to new configurations. That is, before leaving a
\* configuration C, it must make sure that any entry it immediatelyCommitted in T is now
\* immediatelyCommitted by the rules of configuration C i.e. it is "immediately immediatelyCommitted"
\* in C. That is, present on some quorum of servers in C that are in term T. 
OplogCommitment(s) == 
    \* The primary has immediatelyCommitted at least one entry in its term, or, no entries
    \* have been immediatelyCommitted yet.
    /\ (immediatelyCommitted = {}) \/ (\E c \in immediatelyCommitted : (c[2] = currentTerm[s]))
    \* All entries immediatelyCommitted in the primary's term are immediatelyCommitted in its current config.
    /\ \A c \in immediatelyCommitted : (c[2] = currentTerm[s]) => IsCommitted(c[1], s)

--------------------------------------------------------------------------------

\*
\* Next state actions.
\*

\* Node 'i', a primary, handles a new client request and places the entry 
\* in its log.    
ClientRequest(i) ==
    /\ state[i] = Primary
    /\ log' = [log EXCEPT ![i] = Append(log[i], currentTerm[i])]
    /\ UNCHANGED <<currentTerm, state, immediatelyCommitted, config, configVersion, configTerm>>

\* Node 'i' gets a new log entry from node 'j'.
GetEntries(i, j) ==
    /\ state[i] = Secondary
    \* Node j must have more entries than node i.
    /\ Len(log[j]) > Len(log[i])
       \* Ensure that the entry at the last index of node i's log must match the entry at
       \* the same index in node j's log. If the log of node i is empty, then the check
       \* trivially passes. This is the essential 'log consistency check'.
    /\ LET logOk == IF Empty(log[i])
                        THEN TRUE
                        ELSE log[j][Len(log[i])] = log[i][Len(log[i])] IN
       /\ logOk \* log consistency check
       \* If the log of node i is empty, then take the first entry from node j's log.
       \* Otherwise take the entry following the last index of node i.
       /\ LET newEntryIndex == IF Empty(log[i]) THEN 1 ELSE Len(log[i]) + 1
              newEntry      == log[j][newEntryIndex]
              newLog        == Append(log[i], newEntry) IN
              /\ log' = [log EXCEPT ![i] = newLog]
    /\ UNCHANGED <<immediatelyCommitted, currentTerm, state, config, configVersion, configTerm>>

\*  Node 'i' rolls back against the log of node 'j'.  
RollbackEntries(i, j) ==
    /\ state[i] = Secondary
    /\ CanRollback(i, j)
    \* Roll back one log entry.
    /\ log' = [log EXCEPT ![i] = SubSeq(log[i], 1, Len(log[i])-1)]
    /\ UNCHANGED <<immediatelyCommitted, currentTerm, state, config, configVersion, configTerm>>

\* Node 'i' gets elected as a primary.
BecomeLeader(i, voteQuorum) == 
    \* Primaries make decisions based on their current configuration.
    LET newTerm == currentTerm[i] + 1 IN
    /\ i \in config[i]
    /\ i \in voteQuorum \* The new leader should vote for itself.
    /\ \A v \in voteQuorum : CanVoteForConfig(v, i, newTerm)
    /\ \A v \in voteQuorum : CanVoteForOplog(v, i, newTerm)
    \* Update the terms of each voter.
    /\ currentTerm' = [s \in Server |-> IF s \in voteQuorum THEN newTerm ELSE currentTerm[s]]
    /\ state' = [s \in Server |->
                    IF s = i THEN Primary
                    ELSE IF s \in voteQuorum THEN Secondary \* All voters should revert to secondary state.
                    ELSE state[s]]
    \* Update config's term upon becoming primary.
    /\ configTerm' = [configTerm EXCEPT ![i] = newTerm]
    /\ UNCHANGED <<log, immediatelyCommitted, config, configVersion>>   
            
\* Primary 'i' commits its latest log entry.
CommitEntry(i, commitQuorum) ==
    LET ind == Len(log[i]) IN
    \* Must have some entries to commit.
    /\ ind > 0
    \* This node is leader.
    /\ state[i] = Primary
    \* The entry was written by this leader.
    /\ log[i][ind] = currentTerm[i]
    \* all nodes have this log entry and are in the term of the leader.
    /\ ImmediatelyCommitted(<<ind,currentTerm[i]>>, commitQuorum)
    \* Don't mark an entry as immediatelyCommitted more than once.
    /\ ~\E c \in immediatelyCommitted : c[1] = ind /\ c[2] = currentTerm[i] 
    /\ immediatelyCommitted' = immediatelyCommitted \cup {<<ind, currentTerm[i]>>}
    /\ UNCHANGED <<currentTerm, state, log, config, configVersion, configTerm>>

\* Action that exchanges terms between two nodes and step down the primary if
\* needed. This can be safely specified as a separate action, rather than
\* occurring atomically on other replication actions that involve communication
\* between two nodes. This makes it clearer to see where term propagation is
\* strictly necessary for guaranteeing safety.
UpdateTerms(i, j) == 
    /\ UpdateTermsExpr(i, j)
    /\ UNCHANGED <<log, immediatelyCommitted, config, configVersion, configTerm>>


\* A reconfig occurs on node i. The node must currently be a leader.
Reconfig(i, newConfig) ==
    /\ state[i] = Primary
    /\ ConfigQuorumCheck(i)
    /\ TermQuorumCheck(i)
    /\ QuorumsOverlap(config[i], newConfig)
    /\ OplogCommitment(i)
    /\ i \in newConfig
    /\ configTerm' = [configTerm EXCEPT ![i] = currentTerm[i]]
    /\ configVersion' = [configVersion EXCEPT ![i] = configVersion[i] + 1]
    /\ config' = [config EXCEPT ![i] = newConfig]
    /\ UNCHANGED <<currentTerm, state, log, immediatelyCommitted>>

\* Node i sends its current config to node j.
SendConfig(i, j) ==
    /\ state[j] = Secondary
    /\ IsNewerConfig(i, j)
    /\ configVersion' = [configVersion EXCEPT ![j] = configVersion[i]]
    /\ configTerm' = [configTerm EXCEPT ![j] = configTerm[i]]
    /\ config' = [config EXCEPT ![j] = config[i]]
    /\ UNCHANGED <<currentTerm, state, log, immediatelyCommitted>>

Init == 
    /\ currentTerm = [i \in Server |-> InitTerm]
    /\ state       = [i \in Server |-> Secondary]
    /\ log = [i \in Server |-> <<>>]
    /\ immediatelyCommitted = {}
    /\ configVersion =  [i \in Server |-> 1]
    /\ configTerm    =  [i \in Server |-> InitTerm]
    /\ \E initConfig \in AllConfigs :
        /\ initConfig # {}
        /\ config = [i \in Server |-> initConfig]


\* Add dummy precondition for now so TLC tags actions by name explicitly.
ClientRequestAction == \E s \in Server : ClientRequest(s)
GetEntriesAction == \E s, t \in Server : GetEntries(s, t)
RollbackEntriesAction == \E s, t \in Server : RollbackEntries(s, t)
BecomeLeaderAction == \E s \in Server : \E Q \in Quorums(config[s]) :  BecomeLeader(s, Q)
CommitEntryAction ==  \E s \in Server :  \E Q \in Quorums(config[s]) : CommitEntry(s, Q)
UpdateTermsActions == \E s,t \in Server : UpdateTerms(s, t)
ReconfigAction == \E s \in Server, newConfig \in AllConfigs : Reconfig(s, newConfig)
SendConfigAction == \E s,t \in Server : SendConfig(s, t)

Next == 
    \/ ClientRequestAction
    \/ GetEntriesAction
    \/ RollbackEntriesAction
    \/ BecomeLeaderAction
    \/ CommitEntryAction
    \/ UpdateTermsActions
    \/ ReconfigAction
    \/ SendConfigAction

--------------------------------------------------------------------------------

\*
\* Correctness properties
\*

OnePrimaryPerTerm == 
    \A s,t \in Server :
        (/\ state[s] = Primary 
         /\ state[t] = Primary
         /\ currentTerm[s] = currentTerm[t]) => (s = t)

LeaderAppendOnly == 
    [][\A s \in Server : state[s] = Primary => Len(log'[s]) >= Len(log[s])]_vars

\* <<index, term>> pairs uniquely identify log prefixes.
LogMatching == 
    \A s,t \in Server : 
    \A i \in DOMAIN log[s] :
        (\E j \in DOMAIN log[t] : i = j /\ log[s][i] = log[t][j]) => 
        (SubSeq(log[s],1,i) = SubSeq(log[t],1,i)) \* prefixes must be the same.

\* When a node gets elected as primary it contains all entries immediatelyCommitted in previous terms.
LeaderCompleteness == 
    \A s \in Server : (state[s] = Primary) => 
        \A c \in immediatelyCommitted : (c[2] < currentTerm[s] => InLog(<<c[1],c[2]>>, s))

\* \* If two entries are immediatelyCommitted at the same index, they must be the same entry.
StateMachineSafety == 
    \A c1, c2 \in immediatelyCommitted : (c1[1] = c2[1]) => (c1 = c2)

\* TODO: Precise liveness specification under dynamic reconfiguration?

--------------------------------------------------------------------------------

CONSTANTS 
    MaxTerm, 
    MaxLogLen,
    MaxConfigVersion

\* State Constraint. Used for model checking only.
StateConstraint == 
    \A s \in Server :
        /\ currentTerm[s] <= MaxTerm
        /\ Len(log[s]) <= MaxLogLen
        /\ configVersion[s] <= MaxConfigVersion

Symmetry == Permutations(Server)

Terms == InitTerm..MaxTerm
LogIndices == 1..MaxLogLen
ConfigVersions == 1..MaxConfigVersion

=============================================================================