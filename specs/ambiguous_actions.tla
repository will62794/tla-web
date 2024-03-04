---- MODULE ambiguous_actions ----
EXTENDS TLC, Naturals

\* Actions with different params that lead to the same state.

VARIABLE x

Args == {1,4}

Init == x = 0

OneAction(a) == x' = (x + a) % 3
SecondAction(a) == x' = (x + a) % 3

Next == 
    \/ \E v \in Args : OneAction(v)
    \/ \E v \in Args : SecondAction(v)
====