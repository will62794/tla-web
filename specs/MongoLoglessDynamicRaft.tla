---- MODULE MongoLoglessDynamicRaft ----
\*
\* Logless protocol for managing configuration state for dynamic reconfiguration
\* in MongoDB replication.
\*

EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC

CONSTANTS Server, Secondary, Primary, Nil

VARIABLE currentTerm
VARIABLE state
VARIABLE configVersion
VARIABLE configTerm
VARIABLE config

vars == <<currentTerm, state, configVersion, configTerm, config>>

\* Helper operators.
Quorums(S) == {i \in SUBSET(S) : Cardinality(i) * 2 > Cardinality(S)}
QuorumsAt(i) == Quorums(config[i])
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
Max(s) == CHOOSE x \in s : \A y \in s : x >= y
Empty(s) == Len(s) = 0

Init == 
    /\ currentTerm = [i \in {"s0","s1"} |-> 0]
    /\ state       = [i \in {"s0","s1"} |-> "Secondary"]
    /\ configVersion =  [i \in {"s0","s1"} |-> 1]
    /\ configTerm    =  [i \in {"s0","s1"} |-> 0]
    /\ \E initConfig \in SUBSET {"s0","s1"} : initConfig # {} /\ config = [i \in {"s0","s1"} |-> initConfig]

Next ==
    \/ \E i \in {"s0","s1"}, j \in {"s0","s1"} :
        /\ currentTerm[i] > currentTerm[j]
        /\ currentTerm' = [currentTerm EXCEPT ![j] = currentTerm[i]]
        /\ state' = [state EXCEPT ![j] = "Secondary"]
        /\ configVersion' = configVersion
        /\ configTerm' = configTerm
        /\ config' = config
    \/ \E i \in {"s0","s1"}, newConfig \in SUBSET {"s0","s1"} :
       \E Qa \in {s \in SUBSET config[i] : Cardinality(s) * 2 > Cardinality(config[i])} :
       \E Qb \in {s \in SUBSET config[i] : Cardinality(s) * 2 > Cardinality(config[i])} :
        /\ state[i] = "Primary"
        /\ i \in newConfig
        /\ \A t \in Qa : configVersion[t] = configVersion[i] /\ configTerm[t] = configTerm[i]
        /\ \A t \in Qb : currentTerm[t] = currentTerm[i] 
        /\ \A qx \in {sa \in SUBSET config[i] : Cardinality(sa) * 2 > Cardinality(config[i])}, qy \in {sb \in SUBSET newConfig : Cardinality(sb) * 2 > Cardinality(newConfig)} : qx \cap qy # {}  
        /\ configTerm' = [configTerm EXCEPT ![i] = currentTerm[i]]
        /\ configVersion' = [configVersion EXCEPT ![i] = configVersion[i] + 1]
        /\ config' = [config EXCEPT ![i] = newConfig]
        /\ currentTerm' = currentTerm
        /\ state' = state
    \/ \E i \in {"s0","s1"}, j \in {"s0","s1"} :
        /\ state[j] = "Secondary"
        /\ \/ configTerm[i] > configTerm[j]
           \/ /\ configTerm[i] = configTerm[j]
              /\ configVersion[i] > configVersion[j]
        /\ configVersion' = [configVersion EXCEPT ![j] = configVersion[i]]
        /\ configTerm' = [configTerm EXCEPT ![j] = configTerm[i]]
        /\ config' = [config EXCEPT ![j] = config[i]]
        /\ currentTerm' = currentTerm
        /\ state' = state
    \/ \E i \in {"s0","s1"} : \E voteQuorum \in {s \in SUBSET config[i] : Cardinality(s) * 2 > Cardinality(config[i])} :
        /\ i \in config[i]
        /\ i \in voteQuorum
        /\ currentTerm' = [s \in {"s0","s1"} |-> IF s \in voteQuorum THEN currentTerm[i] + 1 ELSE currentTerm[s]]
        /\ state' = [s \in {"s0","s1"} |->
                        IF s = i THEN "Primary"
                        ELSE IF s \in voteQuorum THEN "Secondary"
                        ELSE state[s]]
        /\ configTerm' = [configTerm EXCEPT ![i] = currentTerm[i] + 1]
        /\ config' = config
        /\ configVersion' = configVersion

Spec == Init /\ [][Next]_vars

=============================================================================

\* Next ==
\*     \/ \E s \in Server, newConfig \in SUBSET Server : Reconfig(s, newConfig)
\*     \/ \E s,t \in Server : SendConfig(s, t)
\*     \/ \E i \in Server : \E Q \in Quorums(config[i]) :  BecomeLeader(i, Q)
\*     \/ \E s,t \in Server : UpdateTerms(s,t)

        \* /\ ConfigQuorumCheck(i)
        \* /\ TermQuorumCheck(i)
        \* /\ QuorumsOverlap(config[i], newConfig)

\* /\ \A v \in voteQuorum : 
\*     /\ currentTerm[v] < currentTerm[i] + 1
\*         \/ configTerm[i] = configTerm[v] /\ configVersion[i] = configVersion[v]
\*         \/ \/ configTerm[i] > configTerm[v]
\*            \/ configTerm[i] = configTerm[v] /\ configVersion[i] > configVersion[v]


(*****

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
    
\* Do all quorums of set x and set y share at least one overlapping node.
QuorumsOverlap(x, y) == \A qx \in Quorums(x), qy \in Quorums(y) : qx \cap qy # {}

\* A quorum of servers in the config of server i have i's config.
ConfigQuorumCheck(i) ==
    \E Q \in Quorums(config[i]) : \A t \in Q : 
        /\ configVersion[t] = configVersion[i]
        /\ configTerm[t] = configTerm[i]

\* A quorum of servers in the config of server i have the term of i.
TermQuorumCheck(i) ==
    \E Q \in Quorums(config[i]) : \A t \in Q : currentTerm[t] = currentTerm[i]    

-------------------------------------------------------------------------------------------

\*
\* Next state actions.
\*

\* Update terms if node 'i' has a newer term than node 'j' and ensure 'j' reverts to Secondary state.
UpdateTermsExpr(i, j) ==
    /\ currentTerm[i] > currentTerm[j]
    /\ currentTerm' = [currentTerm EXCEPT ![j] = currentTerm[i]]
    /\ state' = [state EXCEPT ![j] = Secondary]

UpdateTerms(i, j) == 
    /\ UpdateTermsExpr(i, j)
    /\ UNCHANGED <<configVersion, configTerm, config>>

BecomeLeader(i, voteQuorum) == 
    \* Primaries make decisions based on their current configuration.
    LET newTerm == currentTerm[i] + 1 IN
    /\ i \in config[i]
    /\ i \in voteQuorum
    /\ \A v \in voteQuorum : CanVoteForConfig(v, i, newTerm)
    \* Update the terms of each voter.
    /\ currentTerm' = [s \in Server |-> IF s \in voteQuorum THEN newTerm ELSE currentTerm[s]]
    /\ state' = [s \in Server |->
                    IF s = i THEN Primary
                    ELSE IF s \in voteQuorum THEN Secondary \* All voters should revert to secondary state.
                    ELSE state[s]]
    \* Update config's term on step-up.
    /\ configTerm' = [configTerm EXCEPT ![i] = newTerm]
    /\ UNCHANGED <<config, configVersion>>    

\* A reconfig occurs on node i. The node must currently be a leader.
Reconfig(i, newConfig) ==
    /\ state[i] = Primary
    /\ ConfigQuorumCheck(i)
    /\ TermQuorumCheck(i)
    /\ QuorumsOverlap(config[i], newConfig)
    /\ i \in newConfig
    /\ configTerm' = [configTerm EXCEPT ![i] = currentTerm[i]]
    /\ configVersion' = [configVersion EXCEPT ![i] = configVersion[i] + 1]
    /\ config' = [config EXCEPT ![i] = newConfig]
    /\ UNCHANGED <<currentTerm, state>>

\* Node i sends its current config to node j.
SendConfig(i, j) ==
    /\ state[j] = Secondary
    /\ IsNewerConfig(i, j)
    /\ configVersion' = [configVersion EXCEPT ![j] = configVersion[i]]
    /\ configTerm' = [configTerm EXCEPT ![j] = configTerm[i]]
    /\ config' = [config EXCEPT ![j] = config[i]]
    /\ UNCHANGED <<currentTerm, state>>

****)

