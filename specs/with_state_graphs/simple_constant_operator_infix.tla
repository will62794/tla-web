---- MODULE simple_constant_operator_infix ----
EXTENDS Naturals

VARIABLE x

CONSTANT _|_

NewOp(a,b) == a + b 

Init == x = 5 | 44
Next == x' = x
====