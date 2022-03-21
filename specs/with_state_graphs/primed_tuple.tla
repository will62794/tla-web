---- MODULE primed_tuple ----
EXTENDS TLC, Naturals

VARIABLE x
VARIABLE y

Init == x = 0 /\ y = 0
Next == UNCHANGED <<x,y>>
    
====