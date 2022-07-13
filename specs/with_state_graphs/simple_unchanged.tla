---- MODULE simple_unchanged ----

VARIABLE x
VARIABLE y

vars == <<x,y>>

Init == x = 0 /\ y = 1

Next == UNCHANGED vars

====