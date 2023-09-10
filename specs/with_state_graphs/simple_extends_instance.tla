---- MODULE simple_extends_instance ----
EXTENDS Sequences, Naturals

INSTANCE simple_extends_import

M == INSTANCE simple_extends_import

VARIABLES x

Init == 
    \/ x = ExternalExpr
    \/ x = M!ExternalExpr + 3

Next == x' = x

====