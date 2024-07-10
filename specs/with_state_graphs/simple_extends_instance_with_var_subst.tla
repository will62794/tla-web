---- MODULE simple_extends_instance_with_var_subst ----
EXTENDS Sequences, Naturals

VARIABLES x

INSTANCE simple_extends_M5 WITH m <- x

Init == 
    \/ x = 3 
    \/ MVarInitZero

Next == x' = x

====