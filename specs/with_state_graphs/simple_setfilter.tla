----------------------- MODULE simple_setfilter ------------------------
EXTENDS Naturals

VARIABLE x

Init == x = {c \in {1,2,3} : c > 1}

Next == x' = x 
====