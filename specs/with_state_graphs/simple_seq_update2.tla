---- MODULE simple_seq_update2 ----
EXTENDS Naturals

\* See https://github.com/will62794/tla-web/issues/25.

VARIABLE seq

Init ==
    /\ seq = <<1, 2, 3>>

Next ==
    /\ seq' = [ i \in DOMAIN seq |->
    	IF i = 1 THEN
        	IF seq[1] = 5 THEN 1 ELSE seq[1] + 1
        ELSE seq[i]]

Spec == Init /\ [][Next]_seq

====