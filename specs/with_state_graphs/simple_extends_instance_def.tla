---- MODULE simple_extends_instance_def ----
EXTENDS Sequences, Naturals

M == INSTANCE simple_extends_M1

VARIABLES x

Init == 
    \/ x = M!ExprM1 + 3

Next == x' = x

====