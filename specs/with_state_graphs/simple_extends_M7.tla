---- MODULE simple_extends_M7 ----
EXTENDS Sequences, Naturals

VARIABLE m, n

E5 == 45

MInit == 
    /\ m = E5 
    /\ n = 33

A1 == (m' = (m + 1) % 3) /\ UNCHANGED n

====