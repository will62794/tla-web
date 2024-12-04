---- MODULE operator_name_clash_test ----
EXTENDS Naturals

VARIABLES x

Op(x) == x + 2

Init == x = 0
Next == x' = Op(x)

====