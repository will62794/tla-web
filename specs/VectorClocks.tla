--------------- MODULE VectorClocks ---------------

\* Original source: https://github.com/nano-o/vector-clocks/blob/main/VectorClocks.tla

EXTENDS Integers, Sequences, FiniteSets

MaxPair(n1, n2) == IF n1 > n2 THEN n1 ELSE n2

(*************************)
(* Stuff about relations *)
(*************************)

Domain(R) == {r[1] : r \in R}

Image(R) == {r[2] : r \in R}

TransitiveClosure(R) == R \cup
    {r \in Domain(R) \times Image(R) :
        \E z \in Domain(R) : <<r[1], z>> \in R /\ <<z, r[2]>> \in R}

CONSTANT
    P \* the set of processes

CONSTANT IntSet

VectorClock == [P -> IntSet]
v1 \preceq v2 == \A p \in P : v1[p] <= v2[p]
v1 \prec v2 == v1 \preceq v2 /\ \E p \in P : v1[p] < v2[p]

Msg == [sender : P, clock : VectorClock]

Event == (P \times {"send", "deliver"} \times Msg) \cup (P \times {"init"})
EventOrdering == SUBSET (Event \times Event)

VARIABLES
    happensBefore \* a ghost variable tracking the happens-before relation
,   clock \* the vector clock
,   sent \* the set of messages sent
,   localEvents

TypeOK ==
    /\  happensBefore \in EventOrdering
    /\  clock \in [P -> VectorClock]
    /\  sent \in SUBSET Msg
    /\  localEvents \in [P -> SUBSET Event]

zero == [p \in P |-> 0]

Init ==
    /\ happensBefore = {}
    /\ clock = [p \in P |-> zero]
    /\ sent = {}
    /\ localEvents = [p \in P |-> {<<p, "init">>}]

MergeClocks(c1, c2) == [p \in P |-> MaxPair(c1[p], c2[p])]
StepClock(p, vc) == [vc EXCEPT ![p] = @ + 1]
DeliverableAt(m, p) ==
    \A k \in P :
        /\ k = m.sender => m.clock[k] = clock[p][k] + 1
        /\ k # m.sender => m.clock[k] <= clock[p][k]

SendEvent(m) == <<m.sender, "send", m>>
DeliveryEvent(p, m) == <<p, "deliver", m>>

Deliver(p, m) ==
    /\  m \in sent
    /\  DeliverableAt(m, p)
    /\  LET d == DeliveryEvent(p, m)
            s == SendEvent(m)
        IN
        /\  localEvents' = [localEvents EXCEPT ![p] = @ \cup {d}]
        /\  happensBefore' = TransitiveClosure({<<s, d>>}
                \cup {<<e, d>> : e \in localEvents[p]} \cup happensBefore)
    /\  clock' = [clock EXCEPT ![p] = MergeClocks(@, m.clock)]
    /\  UNCHANGED sent

Send(p) ==
    /\  clock' = [clock EXCEPT ![p] = StepClock(p, @)]
    /\  LET m == [sender |-> p, clock |-> clock'[p]]
            s == SendEvent(m)
        IN
        /\  sent' = sent \cup {m}
        /\  localEvents' = [localEvents EXCEPT ![p] = @ \cup {s}]
        /\  happensBefore' = 
                TransitiveClosure({<<e, s>> : e \in localEvents[p]} \cup happensBefore)

Next ==
    \/  \E p \in P : Send(p) 
    \/  \E p \in P : \E m \in Msg : Deliver(p, m)

vars == <<happensBefore, clock, sent, localEvents>>
Spec == 
    /\  Init /\ [][Next]_vars 
    /\  \A p \in P, m \in Msg : WF_vars(Deliver(p, m))

ReflectsAndPreserve ==
    \A m1,m2 \in sent :
        (m1.clock \prec m2.clock) = (<<SendEvent(m1), SendEvent(m2)>> \in happensBefore)

CausalDelivery == \A p \in P :
    \A e1,e2 \in localEvents[p] :
        /\  e1[2] = "deliver"
        /\  e2[2] = "deliver"
        =>  LET m1 == e1[3]
                m2 == e2[3]
            IN  <<SendEvent(m1), SendEvent(m2)>> \in happensBefore
                => <<e1,e2>> \in happensBefore

Liveness == \A m \in Msg : \A p \in P :
    [](m \in sent /\ m.sender # p => <>(DeliveryEvent(p,m) \in localEvents[p]))

Canary == \neg (
    \E p \in P, q \in P : p # q /\ clock[p][q] > 0
)

CONSTANT IntMax
MyInts == 0..IntMax

Constraint ==
    \A p1,p2 \in P : clock[p1][p2] < IntMax


=============================================================================