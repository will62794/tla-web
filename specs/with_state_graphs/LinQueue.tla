----------------------------- MODULE LinQueue -------------------------------
EXTENDS Naturals, Sequences, TLC

opInvocations == {"E", "D"}
opResponse == "Ok"

Values == {"x", "y", "z"} 
Processes == {"A", "B", "C"}

\* Process subhistory
H|P == SelectSeq(H, LAMBDA e : e.proc = P)

PossibleResponses(e) ==
    CASE e.op = "E" -> {[op|->"Ok", proc|->e.proc]}
      [] e.op = "D" -> [op:{"Ok"}, proc:{e.proc}, val:Values]

IsInvocation(e) == e.op \in opInvocations
IsResponse(e) == e.op = opResponse

Matches(H, i, j) ==
    /\ H[i].proc = H[j].proc
    /\ H[i].op \in opInvocations
    /\ H[j].op = opResponse
    /\ "val" \in DOMAIN H[j] <=> H[i].op = "D" \* Only dequeues have values in the response
    /\ ~\E k \in (i+1)..(j-1) : H[k].proc = H[i].proc


RECURSIVE LegalQueue(_, _)

\* Check if a history h is legal given an initial queue state q
LegalQueue(h, q) == \/ h = << >>
                    \/ LET first == Head(h)
                           rest == Tail(h)
                       IN \/ /\ first.op = "E" 
                             /\ LegalQueue(rest, Append(q, first.val))
                          \/ /\ first.op = "D"
                             /\ Len(q)>0
                             /\ first.val = Head(q)
                             /\ LegalQueue(rest, Tail(q))

IsLegalQueueHistory(h) == LegalQueue(h, << >>)

\* Given a sequential history H, true if it represents a legal queue history
IsLegal(H) == 
    LET RECURSIVE Helper(_, _)
        Helper(h, s) == IF h = << >> THEN IsLegalQueueHistory(s)
                        ELSE LET hr == Tail(Tail(h))
                                 inv == h[1]
                                 res == h[2]
                                 e == [op|->inv.op, val|-> IF inv.op = "E" THEN inv.val ELSE res.val]
                             IN Helper(hr, Append(s, e))
    IN Helper(H, <<>>)

L == INSTANCE Linearizability

IsLinearizableHistory(H) == L!IsLinearizableHistory(H)
IsLin(H) == IsLinearizableHistory(H) \* Shorter alias

Linearize(H) == L!Linearize(H)

=============================================================================
