------------------------------- MODULE EWD998_regression1 -------------------------------
EXTENDS Integers

N == 2

Node == 0 .. N-1

Color == {"white", "black"}

VARIABLES 
    active,
    pending,
    color,
    counter,
    token

vars == <<active, pending, color, counter, token>>

-----------------------------------------------------------------------------

Init ==
    /\ active \in [Node -> BOOLEAN]
    /\ pending = [i \in Node |-> 0]
    (* Rule 0 *)
    /\ color \in [Node -> {"white"}]
    /\ counter = [i \in Node |-> 0]
    \* TODO: Address bug with repeated assignment here.
    \* /\ pending = [i \in Node |-> 0]
    /\ token = [pos |-> 0, q |-> 0, color |-> "black"]

Next == UNCHANGED <<active, pending, color, counter, token>>
=============================================================================