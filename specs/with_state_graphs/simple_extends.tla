---- MODULE simple_extends ----
EXTENDS Sequences, simple_extends_M1, simple_extends_M2

VARIABLES x

Init == 
    \/ x = ExprM1
    \/ x = ExprM2

Next == x' = x

====