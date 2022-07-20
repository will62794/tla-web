---- MODULE simple_unchanged_nested_def ----

VARIABLE x
VARIABLE y

\* TODO: Make sure this works for the right reasons in UNCHANGED evaluation?
vars == <<x,y>>
vars1 == vars
vars2 == vars1

Init == x = 0 /\ y = 1

Next == UNCHANGED vars2

====