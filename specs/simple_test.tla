----------------------- MODULE simple_test ------------------------
EXTENDS Naturals

VARIABLE x
VARIABLE y

Init == 
    /\ x = 0
    /\ y = 0

Add == UNCHANGED <<x,y>>

Next == Add



=============================================================================