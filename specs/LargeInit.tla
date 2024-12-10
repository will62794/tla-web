---- MODULE LargeInit ----

\* Spec with many initial states.

VARIABLE x,y,z

N == 11

Init == 
    /\ x \in [a : 1..N, b : 1..N, c : 1..N]
    /\ y \in 1..N
    /\ z \in 1..N

Next == 
    /\ x' = x
    /\ y' = y
    /\ z' = z

====
