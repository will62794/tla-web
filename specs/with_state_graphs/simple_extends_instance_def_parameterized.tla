---- MODULE simple_extends_instance_def_parameterized ----
EXTENDS Sequences, Naturals

M(a, b) == INSTANCE simple_extends_M4 WITH Val <- a, ValB <- b * 5

VARIABLES x, y

E1 == 45

Init == 
    /\ x = M(11, 12)!ExprM4 + M(21, E1 + 1)!ExprM4_B + 3
    /\ y = 12

Next == x' = x /\ y' = y

====