---- MODULE simple_tlc_fn_compose ----
EXTENDS TLC

VARIABLES x

Init ==
    \/ x = (0 :> 11)
    \/ x = (1 :> 33) @@ (2 :> 55)
    \* Test other values that can be interpreted as functions.
    \/ x = <<3,4>> @@ (10 :> 55)
    \/ x = (10 :> 55) @@ <<3,4>>
    \/ x = [a |-> 1, b |-> 2] @@ ("c" :> 55 @@ "d" :> 66)

Next == UNCHANGED <<x>>

====