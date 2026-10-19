---- MODULE exists_over_disjunction ----
EXTENDS Naturals

CONSTANT N

P == 1..N

VARIABLES left, right

Init ==
    /\ left = {}
    /\ right = {}

SetLeft(p) ==
    /\ p \notin left
    /\ left' = left \cup {p}
    /\ UNCHANGED right

SetRight(p) ==
    /\ p \notin right
    /\ right' = right \cup {p}
    /\ UNCHANGED left

Clear(p) ==
    /\ p \in left
    /\ p \in right
    /\ left' = left \ {p}
    /\ right' = right \ {p}

Next ==
    \E p \in P:
        \/ SetLeft(p)
        \/ SetRight(p)
        \/ Clear(p)

====
