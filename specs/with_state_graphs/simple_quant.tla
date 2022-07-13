----------------------- MODULE simple_quant ------------------------
EXTENDS Naturals

VARIABLE x
\* Init == x = 0
\* Init == x = (\E i \in {1,2,3} : i > 2)

Init == 
    x = [ exists1 |-> \E i \in {1,2,3} : i > 2,
          exists2 |-> \E i \in {1,2,3} : i = 4,
          forall1 |-> \A i \in {1,2,3} : i > 2,
          forall2 |-> \A i \in {1,2,3} : i < 5]

Next == x' = x 

\* /\ y' = y
====