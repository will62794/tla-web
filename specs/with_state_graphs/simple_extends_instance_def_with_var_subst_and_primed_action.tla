---- MODULE simple_extends_instance_def_with_var_subst_and_primed_action ----
EXTENDS Sequences, Naturals

VARIABLES x,y

M == INSTANCE simple_extends_M7 WITH m <- x, n <- y

Init == 
    \/ x = 5 /\ y = 12
    \/ M!MInit

Next == 
    /\ M!A1

====