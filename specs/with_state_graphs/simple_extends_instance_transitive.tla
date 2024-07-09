---- MODULE simple_extends_instance_transitive ----
EXTENDS Sequences, Naturals

INSTANCE simple_extends_M1

VARIABLES x

Init == 
    \/ x = ExprM1 + 3

Next == x' = x

====