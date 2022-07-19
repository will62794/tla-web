----------------------- MODULE simple_record ------------------------
EXTENDS Sequences
VARIABLE x
Init == x = [
    rec1 |-> [a |-> 1, b |-> 2],
    rec2 |-> LET r1 == [a |-> 1, b |-> 2] IN r1.a,
    rec3 |-> LET r1 == [a |-> 1, b |-> 2] IN r1.b
]
Next == x' = x
====