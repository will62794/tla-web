----------------------- MODULE simple2 ------------------------
VARIABLE x
Init == x = 1 \/ x = 2 
Next == x' = 2
====