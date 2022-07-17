---- MODULE simple_conjunction_constant ----

\* Test a variety of disjunctions (e.g. \/, \E, \in, etc.) in constant expressions.

VARIABLE x

Init == 
    /\ x = [
            forall1 |-> \A i \in {1,2,3} : i = 2,
            forall2 |-> \A i,j \in {1,2,3} : i = 2 /\ j = 3,
            and1 |-> TRUE /\ FALSE /\ TRUE,
            conjlist1 |-> (
                /\ TRUE
                /\ FALSE
                /\ TRUE
            ),
            bottom |-> FALSE
        ]  

Next == x' = x

====