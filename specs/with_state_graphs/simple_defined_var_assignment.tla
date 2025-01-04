---- MODULE simple_defined_var_assignment ----

VARIABLE x
VARIABLE y

vars == <<x,y>>

c == x
a == c

Init == c = 0 /\ y = 1

Next == UNCHANGED <<x,y>>

====