---- MODULE simple_boolean ----
EXTENDS Naturals
\* Test a variety of disjunctions (e.g. \/, \E, \in, etc.) in constant expressions.

VARIABLE x

Init == 
    \/ FALSE /\ x = 0
    \/ TRUE /\ x = 0
    \/ FALSE /\ x = 0 + "a"

Next == 
    \/ 3 > 4 /\ x' = 5 + "a"
    \/ 3 < 4 /\ x' = 5

====