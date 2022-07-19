---- MODULE simple_var_tuple ----

VARIABLE x
VARIABLE y

vars == <<x,y>>

Init == x = 0 /\ y = 1

Next == UNCHANGED <<x,y>>

====