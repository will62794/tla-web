---- MODULE simple_extends_instance ----
EXTENDS Sequences, Naturals

INSTANCE simple_extends_M3

VARIABLES x

Init == 
    \/ x = ExprM3 + 3

Next == x' = x

====