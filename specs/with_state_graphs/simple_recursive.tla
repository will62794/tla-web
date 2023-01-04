---- MODULE simple_recursive ----
EXTENDS Naturals, Sequences

VARIABLE x

RECURSIVE SeqSum(_)
SeqSum(s) == IF Len(s) = 0 THEN 0 ELSE Head(s) + SeqSum(Tail(s))

RECURSIVE Sum(_)
Sum(S) == IF S = {} THEN 0
                    ELSE LET a == CHOOSE v \in S : TRUE
                         IN  a + Sum(S \ {a})

Init == 
    \/ x = SeqSum(<<1,6,12,18>>)
    \/ x = Sum({1,3,6,9})
    
Next == x' = x

====