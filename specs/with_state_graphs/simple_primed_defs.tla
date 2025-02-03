---- MODULE simple_primed_defs ----
VARIABLES var, var2

D1 == var2

vars == <<var>>
Init ==
    /\ var = 0
    /\ var2 = 6

Action ==
    /\ LET vdef == var IN vdef' = 1
    /\ D1' = 15

Next == Action

Spec == /\ Init /\ [][Next]_vars
====