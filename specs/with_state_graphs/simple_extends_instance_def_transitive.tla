---- MODULE simple_extends_instance_def_transitive ----
EXTENDS Sequences, Naturals

M == INSTANCE simple_extends_M1

VARIABLES x

Init == 
    \* ExprM1 in references another definition inside
    \* simple_extends_M1, so we are testing that these definitions
    \* can be correctly resolved.
    \/ x = M!ExprM1 + 3

Next == x' = x

====