---- MODULE simple_extends_with_var_and_const ----
EXTENDS Sequences, A1_var_y_const_d

VARIABLES x

Init == 
    \/ x = 2 + d /\ InitY
    \/ x = 5 + d /\ InitY

Next == x' = x /\ y' = y

====