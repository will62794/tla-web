---- MODULE simple_extends_instance_with_var_subst_identity ----
EXTENDS Sequences, Naturals

VARIABLES m

INSTANCE simple_extends_M5 WITH m <- m

Init == 
    \/ m = 3 
    \/ MVarInitZero

Next == m' = m

====