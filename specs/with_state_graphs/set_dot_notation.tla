---- MODULE set_dot_notation ----
EXTENDS TLC, Naturals

VARIABLE x

Init == x = 1..3
Next == x' = x
    
====