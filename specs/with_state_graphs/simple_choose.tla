---- MODULE simple_choose ----
EXTENDS Naturals

VARIABLE x

Max(S) == CHOOSE m \in S : \A y \in S : m >= y

\* TODO: CHOOSE may not currently match TLC's behavior in general
\* when there are multiple values satisfying the CHOOSE condition. 
Init == 
    \/ x = CHOOSE a \in {1,2,3} : a = 2
    \/ x = Max({6,1,3,4,5})
    \/ x = Max({1,2,8,8,3})
    
Next == 
    /\ x' = x

====