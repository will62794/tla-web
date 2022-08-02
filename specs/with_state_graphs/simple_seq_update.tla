---- MODULE simple_seq_update ----
EXTENDS Naturals

\* See https://github.com/will62794/tla-web/issues/25.

VARIABLE seq

Init ==
    /\ seq = <<1, 2, 3>>

Next ==
    /\ seq' = [seq EXCEPT ![1] = IF @ = 5 THEN 1 ELSE @ + 1]

Spec == Init /\ [][Next]_seq

====