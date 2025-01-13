---- MODULE simple_fcn_def ----
EXTENDS Naturals, TLC

VARIABLE x
VARIABLE y

\* Function definition.
f2[a,b \in {1,3}, c \in {6,9}] == a + b + c
f4[a \in {1,3}] == a + a

fact[a \in {1,2,3,4}] == IF a = 1 THEN 1 ELSE a * fact[a-1]
sum[a \in {1,2,3,4}] == IF a = 1 THEN 1 ELSE a + sum[a-1]

Init == 
    /\ y = 7
    /\ x = ([
            e |-> f2[3,1,9],
            d |-> f4[3],
            f |-> fact[3],
            g |-> sum[4]
        ])

Next == x' = x /\ y' = y

====