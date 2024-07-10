---- MODULE simple_extends_instance_with_var_and_const_subst_transitive ----
EXTENDS Sequences, Naturals

VARIABLES x

INSTANCE simple_extends_M5b WITH mb <- x

Init == 
    \/ x = 1 
    \/ MbVarInitZero

Next == x' = x

====