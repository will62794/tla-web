---- MODULE simple_extends_M5b ----
EXTENDS Sequences

VARIABLE mb

INSTANCE simple_extends_M6 WITH V <- 113, m <- mb

MbVarInitZero == 
    \/ mb = 0
    \/ MVarInitZero

====