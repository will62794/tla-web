---- MODULE simple_extends_instance_def_user_infix_op ----
EXTENDS Sequences, Naturals

M == INSTANCE simple_extends_M2c

VARIABLES x

Init == 
    \/ x = M!++(33,12)

Next == x' = x

====