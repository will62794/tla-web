---- MODULE simple_extends_instance_with_var_and_const_subst ----
EXTENDS Sequences, Naturals

VARIABLES x

INSTANCE simple_extends_M6 WITH V <- 34, m <- x

Init == 
    \/ x = 3 
    \/ MVarInitZero

Next == x' = x

====