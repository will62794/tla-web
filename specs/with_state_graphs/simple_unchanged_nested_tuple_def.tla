---- MODULE simple_unchanged_nested_tuple_def ----
EXTENDS Naturals

VARIABLE x
VARIABLE y
VARIABLE z

zvar == (<<(z)>>)
unchangedVars == <<y,((zvar))>>

Init == 
    /\ x = 0 
    /\ y = 1
    /\ z = 2

Next == 
    /\ x' = (x + 1) % 2
    /\ UNCHANGED <<unchangedVars>>

====