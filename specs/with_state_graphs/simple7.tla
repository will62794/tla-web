----------------------- MODULE simple7 ------------------------
VARIABLE x
Init == x = 0
Next == x' \in {0,1,2,3} /\ x' # x
====