---- MODULE simple_domain ----
EXTENDS Sequences

VARIABLES x

Init == x = DOMAIN <<>>

Next == x' = x

====