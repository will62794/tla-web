----------------------- MODULE simple_add ------------------------
EXTENDS Naturals

VARIABLE x
Init == 
    \/ (x = 1 + 2 + 4) 
    \/ (x = {1,2,3} \cap {2,3})
    \/ x = 6
Next == x' = x
====