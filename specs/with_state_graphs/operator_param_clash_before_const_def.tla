------------------------- MODULE operator_param_clash_before_const_def ------------------------------
EXTENDS Naturals

Intersect(s, c) == s \intersect c

CONSTANT c

VARIABLES x

Init ==
    /\ x = c

Next ==
    /\ x' = Intersect(1..3, 3..4)

vars == <<x>>
Spec == Init /\ [][Next]_vars

===============================================================================