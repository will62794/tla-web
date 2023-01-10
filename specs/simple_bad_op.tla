---- MODULE simple_bad_op ----
EXTENDS TLC, Naturals, Integers, Sequences, FiniteSets

VARIABLE x

Init ==
    \/ x = \E a,
              b,
              c,
              d \in {1,2,3}:
              a = 2 
    \/ x = 2 + UnknownOp(2)
Next == UNCHANGED x

====