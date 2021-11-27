---- MODULE test1 ----
EXTENDS Naturals

VARIABLE x
VARIABLE y

Init == 
    /\ x = 1 \/ x = 2
    /\ y = 3 \/ y = 4
    /\ x = 5

Next == 
    /\ x = 2 /\ x' = 12
    /\ y = 3 /\ y' = 13

=============================================================================