---- MODULE test_missing_assigned_vars ----
EXTENDS TLC

VARIABLES x, y

Init == x = 1 /\ y = 2

A == x' = 3 /\ y' = 4
B == x' = 5

Next == A \/ B

====