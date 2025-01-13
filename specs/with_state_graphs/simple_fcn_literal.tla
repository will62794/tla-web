---- MODULE simple_fcn_literal ----
EXTENDS Naturals, TLC

VARIABLE x
VARIABLE y

\* Function literal.
f1 == [a,b \in {1,4}, c \in {5,9,8} |-> a + b + c + y]
f1a == [a \in {1,2} |-> a + a]

Init == 
    /\ y = 7
    /\ x = ([
            a |-> f1,
            b |-> f1a
        ])

Next == x' = x /\ y' = y

====