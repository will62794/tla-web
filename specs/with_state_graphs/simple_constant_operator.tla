---- MODULE simple_constant_operator ----
EXTENDS Naturals

VARIABLE x

CONSTANT Op(_)

Op1(a) == a + 5 

Init == x = Op(3)
Next == x' = x
====