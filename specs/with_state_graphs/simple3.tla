----------------------- MODULE simple3 ------------------------
VARIABLE x
VARIABLE y
Init == 
    /\ x = 1 \/ x = 2 
    /\ y = 3 \/ y = 4

Next == x' = 2 /\ y' = 2
====