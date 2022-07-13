---- MODULE mldr_init_only ----
EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC

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

Server == {"n0","n1"}

Init == 
    /\ currentTerm = [i \in Server |-> 0]
    /\ state       = [i \in Server |-> "Secondary"]
    /\ configVersion =  [i \in Server |-> 1]
    /\ configTerm    =  [i \in Server |-> 0]
    /\ \E initConfig \in SUBSET Server : initConfig # {} /\ config = [i \in Server |-> initConfig]

Next == 
    /\ currentTerm' = currentTerm
    /\ state' = state
    /\ configVersion' = configVersion
    /\ configTerm' = configTerm 
    /\ config' = config

============================