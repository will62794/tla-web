---- MODULE counter ----
EXTENDS TLC, Naturals

VARIABLE x

Init == x = 0
Next == x' = x + 1
====