---- MODULE simple_extends_instance_def_with_subst ----
EXTENDS Sequences, Naturals

M == INSTANCE simple_extends_M4 WITH Val <- 45

VARIABLES x

Init == 
    \/ x = M!ExprM4 + 3

Next == x' = x

====