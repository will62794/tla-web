------------------------- MODULE def_before_var_decl ------------------------------
EXTENDS Naturals

Point == {1,2}   \* Set of points {p1, p2, p3}

Proc == {0}

PointRelationType == [Point -> [Point -> BOOLEAN]]

(* Definition of a partial order. *)
IsPartialOrder(leq) ==
    /\ \A s, t, u \in Point : leq[s][t] /\ leq[t][u] => leq[s][u] \* transitive
    /\ \A s, t \in Point : leq[s][t] /\ leq[t][s] => s = t \* antisymmetric
    /\ \A s \in Point : leq[s][s] \* reflexive

PointToNat == [Point -> 0..2]

VARIABLES lleq,nrec,glob

Init ==
    /\ lleq \in PointRelationType
    /\ IsPartialOrder(lleq)               \* Any partial order
    /\ nrec \in PointToNat                \* Any initial record-point arrangement
    /\ glob = [p \in Proc |-> nrec]       \* Initial values


Next ==
    /\ lleq' = lleq 
    /\ nrec' = nrec
    /\ glob' = glob
    


===============================================================================