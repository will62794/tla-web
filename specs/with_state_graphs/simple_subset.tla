----------------------- MODULE simple_subset ------------------------
EXTENDS FiniteSets, Naturals

VARIABLE x

S == {1,2,3,4,5}

Init == 
    \/ x = SUBSET {1,2,3}
    \/ x = [{"x"} -> SUBSET {1,2}]
    \/ x = {i \in SUBSET(S) : Cardinality(i) * 2 > Cardinality(S)}
    
Next == x' = x
====