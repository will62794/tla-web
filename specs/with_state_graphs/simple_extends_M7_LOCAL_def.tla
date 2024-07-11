---- MODULE simple_extends_M7_LOCAL_def ----
EXTENDS Sequences, Naturals

LOCAL InternalExpr == 12
EternalExpr == 14 + InternalExpr

====