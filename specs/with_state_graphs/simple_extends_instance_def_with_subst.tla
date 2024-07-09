---- MODULE simple_extends_instance_def_with_subst ----
EXTENDS Sequences, Naturals

M == INSTANCE simple_extends_M4 WITH Val <- 45, ValB <- 99

VARIABLES x

Init == 
    \/ x = M!ExprM4 + M!ExprM4_B + 3

Next == x' = x

====