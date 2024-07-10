---- MODULE simple_extends_instance_with_const_subst ----
EXTENDS Sequences, Naturals

INSTANCE simple_extends_M4 WITH Val <- 33, ValB <- 66

VARIABLES x

Init == 
    \/ x = ExprM4 + ExprM4_B + 3

Next == x' = x

====