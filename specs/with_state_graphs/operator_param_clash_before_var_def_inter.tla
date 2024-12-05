------------------------- MODULE operator_param_clash_before_var_def_inter ------------------------------
EXTENDS Naturals

Intersect(s, x) ==
    IF s \intersect x # {} THEN 1 ELSE 2

VARIABLES x, v 

Add(a, y) == a + y

VARIABLES y

Init ==
    /\ x = 0
    /\ v = 0
    /\ y = 0

Next ==
    /\ v' = Intersect(1..2, 3..4)
    /\ y' = Add(x, (y + 1) % 3)
    /\ UNCHANGED x

vars == <<x, v>>
Spec == Init /\ [][Next]_vars

===============================================================================