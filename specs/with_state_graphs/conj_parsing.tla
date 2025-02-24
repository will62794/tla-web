---- MODULE conj_parsing ----
EXTENDS TLC, Naturals


VARIABLE x,y,z

Init == x = 1 /\ y = 2 /\ z = 30

Next == 
        /\ x' = (x + 1) % 2
        /\ \E c \in {5,6} : y' = (y + c) % 2
    /\ z' = (z + 1) % 2

vars == <<x, y, z>>

Spec == Init /\ [][Next]_vars

====