---- MODULE record_literal_eval ----
EXTENDS TLC, Naturals

VARIABLE x

Init == 
\/ x = [a |-> "v1", b |-> "v2"]
\/ x = [a |-> "v1", b |-> "v2", c |-> "v3"]
Next == x' = x
    
====