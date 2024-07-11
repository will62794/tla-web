---- MODULE simple_extends_local_def ----
EXTENDS Sequences, simple_extends_M7_LOCAL_def

VARIABLES x

\* A definition with the same name is defined in 'simple_extends_M7_LOCAL_def',
\* but as LOCAL, so it should not conflict with this definition.
InternalExpr == 5

Init == 
    \/ x = InternalExpr + EternalExpr

Next == x' = x

====