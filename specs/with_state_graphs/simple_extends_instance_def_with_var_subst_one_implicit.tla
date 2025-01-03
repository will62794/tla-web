---- MODULE simple_extends_instance_def_with_var_subst_one_implicit ----
EXTENDS Sequences, Naturals

VARIABLES x

C == 5

M == INSTANCE simple_extends_M5c WITH m <- x

Init == 
    \/ x = 5
    \/ M!MVarInitZero

Next == x' = x

====