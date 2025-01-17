---- MODULE simple_extends_with_var ----
EXTENDS Sequences, A1_var_y

VARIABLES x

Init == 
    \/ x = 2 /\ InitY
    \/ x = 5 /\ InitY

Next == x' = x /\ y' = y

====