---- MODULE simple_tlc_fn ----
EXTENDS TLC

VARIABLES
    x,
    y

Init ==
    \/ /\ x = (0 :> 0)
       /\ y = (1 :> 1)
    \/ /\ x = 2 :> 3
       /\ y = 4 :> 5

Next == UNCHANGED <<x, y>>

====