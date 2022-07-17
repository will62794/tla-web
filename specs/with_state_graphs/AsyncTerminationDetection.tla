---------------------- MODULE AsyncTerminationDetection ---------------------
EXTENDS Naturals

N == 1

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
    /\ active \in [ Node -> BOOLEAN ]
    /\ pending \in [ Node -> 0..1 ]
    /\ terminationDetected \in {FALSE, terminated}

Terminate(i) ==
    /\ active' \in { f \in [ Node -> BOOLEAN] : \A n \in Node: ~active[n] => ~f[n] }
    /\ pending' = pending
    /\ terminationDetected' \in {terminationDetected, terminated'}

SendMsg(i, j) ==
    /\ active[i]
    /\ pending' = [pending EXCEPT ![j] = @ + 1]
    /\ UNCHANGED << active, terminationDetected >>

Wakeup(i) ==
    /\ pending[i] > 0
    /\ active' = [active EXCEPT ![i] = TRUE]
    /\ pending' = [pending EXCEPT ![i] = @ - 1]
    /\ UNCHANGED << terminationDetected >>

DetectTermination ==
    /\ terminated
    /\ ~terminationDetected
    /\ terminationDetected' = TRUE
    /\ UNCHANGED << active, pending >>

-----------------------------------------------------------------------------

NMax == 2

Next ==
    \* \/ DetectTermination
    \/ \E i \in Node, j \in Node:   
        \* \/ Terminate(i)
        \* \/ Wakeup(i)
        \* Bound state space for testing.
        \/ \A n \in Node : pending[n] < NMax /\ SendMsg(i, j)
=============================================================================