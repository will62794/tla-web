----------------------- MODULE simple_quant2 ------------------------
EXTENDS Naturals

VARIABLE x

Init == \E c \in SUBSET {0,1} : c # {} /\ x = [i \in {"a"} |-> c]

Next == x' = x 
====