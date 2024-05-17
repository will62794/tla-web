---- MODULE simple_extends_instance_def ----
EXTENDS Sequences, Naturals

M == INSTANCE simple_extends_M3

VARIABLES x

Init == 
    \/ x = M!ExprM3 + 3

Next == x' = x

====