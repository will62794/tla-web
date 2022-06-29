---- MODULE simple_len ----
EXTENDS TLC, Naturals, Sequences

VARIABLES x

Init == x = <<>>

Next == x' = Len(x)

====