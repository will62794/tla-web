---- MODULE simple_fcn ----
EXTENDS Naturals, TLC

VARIABLE x
VARIABLE y

\* Function literal.
f1 == [a,b \in {1,4}, c \in {5,9,8} |-> a + b + c + y]
f1a == [a \in {1,2} |-> a + a]

\* Function definition.
f2[a,b \in {1,3}, c \in {6,9}] == a + b + c
f4[a \in {1,3}] == a + a

fact[a \in {1,2,3,4}] == IF a = 1 THEN 1 ELSE a * fact[a-1]
sum[a \in {1,2,3,4}] == IF a = 1 THEN 1 ELSE a + sum[a-1]

Init == 
    /\ y = 7
    /\ x = ([
            a |-> f1,
            b |-> f2,
            ca |-> f1a[1],
            cb |-> f1a[2],
            cc |-> f1[1,4,5],
            d |-> f4[3],
            e |-> f2[3,1,9],
            f |-> fact[3],
            g |-> sum[4]
        ])

Next == x' = x /\ y' = y

====