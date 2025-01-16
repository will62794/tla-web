----------------------- MODULE simple_lazy ------------------------
EXTENDS Naturals

VARIABLE x

\* Don't need to evaluate 'c' eagerly if it is not actually referenced.
\* in the final expression.
Init == 
    \/ LET c == 1 + "a" IN x = 11
    \/ LET f(a) == a + 2 + "b" IN x = 22

Next == x' = x

=============================================================================