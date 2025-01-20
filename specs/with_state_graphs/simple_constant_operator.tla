---- MODULE simple_constant_operator ----
EXTENDS Naturals

VARIABLE x

CONSTANT Op(_)

NewOp(a) == a + 5 

Init == x = Op(3) + 44
Next == x' = x
====