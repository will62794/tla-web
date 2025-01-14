----------------------- MODULE simple_letin ------------------------
EXTENDS Naturals

VARIABLE x

Init == 
    \/ x = [
            a |-> LET y == 2 IN y + 4,
            b |-> LET y == 2 z == 5 IN (y + z),
            c |-> LET y == 2 
                    z == 6
                    w == y + z IN (y + z + w)
        ]
    \* Operator definitions inside LET IN.
    \/ x = LET Op1(a) == a + 2 IN Op1(16)
    \/ x = LET Op2(a,b) == a + b IN Op2(12,3)
    \/ x = LET Op1(a) == a + 3 
               Op2(u, v) == u + v IN
               Op1(12) * Op2(3, 4)
Next == x' = x 
====