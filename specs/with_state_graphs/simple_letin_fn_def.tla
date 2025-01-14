----------------------- MODULE simple_letin_fn_def ------------------------
EXTENDS Naturals

VARIABLE x

Init == 
    \/ x = LET myfn[a \in {1,2}] == a + 1 IN myfn[2]
Next == x' = x 
====