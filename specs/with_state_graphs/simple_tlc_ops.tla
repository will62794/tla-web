---- MODULE simple_tlc_ops ----
EXTENDS TLC, Naturals

VARIABLES x

Init ==
    \/ x = TLCEval(5 + 5)
    \/ x = TLCEval("a")

Next == UNCHANGED <<x>>

====