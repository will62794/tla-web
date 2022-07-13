---- MODULE simple_quant_multi ----
EXTENDS Naturals
\* See https://github.com/will62794/tla-web/issues/17.

VARIABLE x, y

Init == 
    /\ x = 0
    /\ y = 0

Next == 
    \E i,j \in 1..3:
    	/\ x' = i
        /\ y' = j

====