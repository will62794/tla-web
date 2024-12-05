------------------------- MODULE operator_param_clash_before_var_def ------------------------------
EXTENDS Naturals

Intersect(s, x) ==
    IF s \intersect x # {} THEN 1 ELSE 2

VARIABLES x, v 

Init ==
    /\ x = 0
    /\ v = 0

Next ==
    /\ v' = Intersect(1..2, 3..4)
    /\ UNCHANGED x

vars == <<x, v>>
Spec == Init /\ [][Next]_vars

===============================================================================