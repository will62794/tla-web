----------------------- MODULE simple_letin ------------------------
EXTENDS Naturals

VARIABLE x

Init == 
    x = [
        a |-> LET y == 2 IN y + 4,
        b |-> LET y == 2 z == 5 IN (y + z),
        c |-> LET y == 2 
                  z == 6
                  w == y + z IN (y + z + w)
    ]

Next == x' = x 
====