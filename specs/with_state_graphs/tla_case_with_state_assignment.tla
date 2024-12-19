---- MODULE tla_case_with_state_assignment ----
EXTENDS Naturals

VARIABLE x,y

Init == x = 0 /\ y = 0

Next == 
    CASE 
           (x = 0 /\ y = 0) -> (x' = 1 /\ y' = 1)
        [] (x = 1 /\ y = 1) -> (x' = 2 /\ UNCHANGED <<y>>)
        [] OTHER -> (x' = 0 /\ y' = 0)


====