---- MODULE simple_definition ----
EXTENDS Naturals

VARIABLE x

A == 12
B == 13

\* TODO: CHOOSE may not currently match TLC's behavior in general
\* when there are multiple values satisfying the CHOOSE condition. 
Init == x = A + B
Next == x' = x

====