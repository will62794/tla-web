----------------------- MODULE simple_nondet1 ------------------------
EXTENDS Naturals

Server == {0,1,2}

VARIABLE x

Init == 
    /\ x = 0

Next == 
    \E s \in Server : 
        /\ x < 8
        /\ x' = (x + s) % 12

=============================================================================