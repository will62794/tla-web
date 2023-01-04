---- MODULE simple_recursive ----
EXTENDS Naturals, Sequences

VARIABLE x

RECURSIVE SeqSum(_)
SeqSum(s) == IF Len(s) = 0 THEN 0 ELSE Head(s) + SeqSum(Tail(s))

Init == 
    \/ x = SeqSum(<<1,6,12,18>>)
    
Next == x' = x

====