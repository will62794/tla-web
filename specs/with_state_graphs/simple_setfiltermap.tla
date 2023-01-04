----------------------- MODULE simple_setfiltermap ------------------------
EXTENDS Naturals

VARIABLE x

Init == 
    \/ x = {c \in {1,2,3} : c > 1}
    \/ x = {<<a, b>> : a, b \in 1..3}
    \* \/ x = {<<a, b>> : <<a, b>> \in {1..2} \X {1..2}} // TODO: handle tuple quantification syntax.
    \/ x = {<<a, b>> : a \in 1..3, b \in 1..3}
    \/ x = {<<a, b, c>> : a, b \in 1..3, c \in 6..7}
    \/ x = {<<a+7, b>> : a, b \in 1..3}

Next == x' = x 
====