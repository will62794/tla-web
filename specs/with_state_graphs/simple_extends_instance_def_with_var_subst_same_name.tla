---- MODULE simple_extends_instance_def_with_var_subst_same_name ----
EXTENDS Sequences, Naturals

VARIABLES x

V == 12
i == x
h == x

M == INSTANCE simple_extends_M6 WITH V <- V, m <- h

Init == 
    \/ x = 5
    \/ M!MVarInitZero

Next == x' = x

====