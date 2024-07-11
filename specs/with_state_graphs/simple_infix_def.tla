----------------------- MODULE simple_infix_def ------------------------
EXTENDS Naturals

VARIABLE x

\* Composition
f ** g == [v \in DOMAIN(g) |-> f[g[v]]]

\* Composition
a ++ b == a + b

f1 == [v \in {0,1} |-> v + 2]
f2 == [v \in {2,3} |-> v * 7]


Init == 
    \/ x = 13 ++ 12
    \/ x = f2 ** f1

Next == x' = x

=============================================================================