---- MODULE simple_fcn ----
EXTENDS Naturals

VARIABLE x
VARIABLE y

\* Function literal.
f1 == [a,b \in {1,4}, c \in {5,9,8} |-> a + b + c + y]

\* Function definition.
f2[a,b \in {1,3}, c \in {6,9}] == a + b + c

Init == 
    /\ y = 7
    /\ x = ([
            a |-> f1,
            b |-> f2,
            c |-> f1[1,4,5]
        ])
Next == x' = x /\ y' = y

====