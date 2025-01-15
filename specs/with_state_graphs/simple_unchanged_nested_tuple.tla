---- MODULE simple_unchanged_nested_tuple ----

VARIABLE x
VARIABLE y

\* TODO: Make sure this works for the right reasons in UNCHANGED evaluation?
yvars == <<y>>
vars == <<x,yvars>>

Init == x = 0 /\ y = 1

Next == 
    \/ x' = 1 /\ UNCHANGED yvars
    \/ UNCHANGED vars

====