---- MODULE LogExample_bounded ----

\* From https://github.com/will62794/tla-web/issues/23.

EXTENDS Naturals, Sequences

VARIABLE log, idx

Init ==
    /\ log = <<>>
    /\ idx = 0

IncIdx ==
    /\ idx' = idx + 1
    /\ UNCHANGED log

JumpIdx ==
    /\ idx > 0
    /\ idx' \in 0..Len(log)
    /\ UNCHANGED log

GrowLog ==
    /\ log' = Append(log, idx)
    /\ UNCHANGED idx

Read ==
    IF   idx < Len(log)
    THEN {log[idx]}
    ELSE {}

Next ==
    /\ Len(log) < 2
    /\ idx < 3
    /\ \/ IncIdx
       \/ JumpIdx
       \/ GrowLog

Spec == Init /\ [][Next]_<<log, idx>>


====