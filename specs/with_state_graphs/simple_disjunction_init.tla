---- MODULE simple_disjunction_init ----

\* Test a variety of disjunctions (e.g. \/, \E, \in, etc.) 
\* in initial state generation.

VARIABLE x

Init == 
    \/ (x = 0 \/ x = 1 \/ FALSE)
    \/ x = 2
    \/ FALSE
    
Next == 
    /\ x' = x

====