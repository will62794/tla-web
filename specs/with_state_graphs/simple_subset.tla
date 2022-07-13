----------------------- MODULE simple_subset ------------------------
VARIABLE x
Init == x = 0
Next == x' = 
    [ a |-> SUBSET {1,2,3},
      b |-> [{"x"} -> SUBSET {1,2}]]
====