----------------------- MODULE simple_sets ------------------------
EXTENDS Naturals

VARIABLE x

Init == x = 0
Next == x' = [ 
    union1 |-> {1,2} \cup {2,3,4},
    inter1 |-> {1,2} \cap {2,3,4},
    cross1 |-> {1,2} \X {3,4},
    cross2 |-> {1,2} \times {3,4},
    cross3 |-> {} \times {3,4}
]
====