---- MODULE simple_definition ----
EXTENDS Naturals

VARIABLE x

A == 12
B == 13
C(arg) == arg + 44

\* TODO: CHOOSE may not currently match TLC's behavior in general
\* when there are multiple values satisfying the CHOOSE condition. 
Init == x = A + B + C(15)
Next == x' = x

====