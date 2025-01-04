---- MODULE simple_defined_var_assignment_transitive ----

VARIABLE x
VARIABLE y

vars == <<x,y>>

c == x
a == c

Init == a = 0 /\ y = 1

Next == UNCHANGED <<x,y>>

====