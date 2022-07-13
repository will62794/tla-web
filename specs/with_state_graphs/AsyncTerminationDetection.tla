---------------------- MODULE AsyncTerminationDetection ---------------------
EXTENDS Naturals

N == 2

ASSUME NIsPosNat == N \in Nat \ {0}

Node == 0 .. N-1

VARIABLES 
  active,               \* activation status of nodes
  pending,              \* number of messages pending at a node
  terminationDetected

vars == << active, pending, terminationDetected >>

terminated == \A n \in Node : ~ active[n] /\ pending[n] = 0

-----------------------------------------------------------------------------

Init ==
    \* /\ active \in [ Node -> BOOLEAN ]
    \* /\ pending \in [ Node -> 0..1 ]
    /\ active = [i \in {0} |-> TRUE]
    /\ pending = [i \in {0} |-> TRUE]
    /\ terminationDetected \in {FALSE, terminated}

Next ==
	UNCHANGED vars

====