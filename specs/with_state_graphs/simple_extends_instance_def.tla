---- MODULE simple_extends_instance_def ----
EXTENDS Sequences, Naturals

M == INSTANCE simple_extends_M2

VARIABLES x

Init == 
    \/ x = M!ExprM2 + 3

Next == x' = x

====