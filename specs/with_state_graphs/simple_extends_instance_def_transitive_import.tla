---- MODULE simple_extends_instance_def_transitive_import ----
EXTENDS Sequences, Naturals

M2b == INSTANCE simple_extends_M2b

VARIABLES x

Init == 
    \/ x = M2b!ExprM2b + M2b!M3!ExprM3 + 14

Next == x' = x

====