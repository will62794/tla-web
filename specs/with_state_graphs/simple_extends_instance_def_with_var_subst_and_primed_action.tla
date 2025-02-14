---- MODULE simple_extends_instance_def_with_var_subst_and_primed_action ----
EXTENDS Sequences, Naturals

VARIABLES x

M == INSTANCE simple_extends_M5 WITH m <- x

Init == 
    \/ x = 5
    \/ M!MVarInitZero

Next == 
    /\ M!A1

====