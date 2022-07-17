---- MODULE simple_primed ----
EXTENDS TLC, Naturals

VARIABLE x
VARIABLE y

expr == x + 2

Init == 
    /\ x = 0 
    /\ y = 0
Next == 
    /\ x' = 5
    /\ y ' = expr'
    
====