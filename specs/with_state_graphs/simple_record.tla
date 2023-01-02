----------------------- MODULE simple_record ------------------------
EXTENDS Sequences, Naturals

VARIABLE x
Init == x = [
    rec1 |-> [a |-> 1, b |-> 2],
    rec2 |-> LET r1 == [a |-> 1, b |-> 2] IN r1.a,
    rec3 |-> LET r1 == [a |-> 1, b |-> 2] IN r1.b,
    \* Record update with multi-update fields.
    rec4 |-> LET ra == [pos |-> 1, q |-> 2 ] IN
            [ ra EXCEPT !.pos = @ - 5,
                        !.q   = @ + 2],
    \* Record updated with nested path.
    rec5 |-> LET ra == [pos |-> [a |-> 5], q |-> 2 ] IN
            [ ra EXCEPT !.pos.a = @ + 13,
                        !.q   = @ - 5],
    \* Record updated with mixed dot/function nested path.
    rec6 |-> LET ra == [pos |-> [a |-> 5], q |-> [h |-> 2] ] IN
            [ ra EXCEPT !.pos["a"] = @ + 13,
                        !["q"].h   = @ - 5],
    rec7 |-> [ 
        [pos |-> 0, q |-> 6, color |-> "orange"] 
        EXCEPT !.pos = @ - 1,
               !.q   = @ + 5,
               !.color = IF "white" = "black" THEN "black" ELSE @ ],
    \* Set of records.
    recset1 |-> [a: {1,2}, b: {3,4}],
    recset2 |-> [a: {}, b: {3,4}],
    recset3 |-> [a: {1,2}, c: {3,4}, b: {"x", "y", "z"}]
]
Next == x' = x
====