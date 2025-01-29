---- MODULE simple_boolean ----
EXTENDS Naturals
\* Test a variety of disjunctions (e.g. \/, \E, \in, etc.) in constant expressions.

VARIABLE x

I == 
   \/ x = 2 + (2 * 4) - (12 % 8)
\*    \/ x = 66 + 47 

Init == I
    
Next == 
    \* \/ x > 4 /\ x' = 44
    \* \/ 3 < 4
    /\ \/ x' = 5 + (x % 3) \/ x' = 5 + (x % 3) + 1 
       \/ x' = 5 + (x % 3) + 2 \/ x' = 5 + (x % 3) + 4

====