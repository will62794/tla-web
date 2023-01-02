---- MODULE simple_enabled ----
EXTENDS Naturals

VARIABLE x

Action == x > 0 /\ x' = 2

Action2 == x' = 3

Init == x = 1

Next == 
    /\ ENABLED Action
    /\ Action2

====