---- MODULE seq_append ----
EXTENDS TLC, Sequences ,Naturals

VARIABLE x

Init == x = Append(<<1,2>>,3)
Next == x' = x
    
====