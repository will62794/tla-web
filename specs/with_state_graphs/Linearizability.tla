-------------------------- MODULE Linearizability --------------------------

EXTENDS Naturals, Sequences, Utilities

CONSTANT PossibleResponses(_) \* Argument is a history
CONSTANT IsInvocation(_) \* Argument is event
CONSTANT IsResponse(_) \* Argument is event
CONSTANT Matches(_, _, _) \* Arguments are sequence, index, index
CONSTANT IsLegal(_)
CONSTANT _|_
CONSTANT Processes

\* Transpose a set of sets
\* Collect({{"a","b"}, {"x","y"}}) => {{"x", "a"}, {"x", "b"}, {"a", "y"}, {"b", "y"}} 
RECURSIVE Collect(_)

Collect(S) == 
    IF S = {} THEN {{}} ELSE
    LET s == CHOOSE s \in S : TRUE
        R == Collect(S \ {s})
        er == {<<e,r>> \in s \X R : TRUE }
    IN {{e} \union r : <<e,r>> \in er }

\* Given a history, return the invocations that don't have an associated response
InvocationsWithoutResponses(H) ==
    LET N == Len(H)
        inds == {i \in 1..N : IsInvocation(H[i]) /\ ~\E j \in i+1..N : Matches(H,i,j) }
    IN {H[i] : i \in inds }

\* Return a set with all of the possible sets of events that could
\* be appended to H to extend it by completing operations
Extensions(H) == 
    LET R == { PossibleResponses(inv) : inv \in InvocationsWithoutResponses(H)}
    IN Collect(R)



\* Given a history, return the set of all extended histories
ExtendedHistories(H) == 
    LET Ps(s) == UNION({Perms(x) : x \in SUBSET(s)})
        ExtHistory(s) == { H \o ext : ext \in Ps(s) }
    IN UNION({ExtHistory(s) : s \in Extensions(H)}) 
            \cup IF Extensions(H) = {{}} THEN {H} ELSE {}

\* Two histories H and H’ are equivalent if for every process P, H|P = H’|P.
AreEquivalent(H1,H2) == \A p \in Processes : H1|p = H2|p

\* Set of times (indexes) when an op occurs in a history
OpTimes(H, op) == { i \in 1..Len(H) : H[i] = op }

\* Set of pairs of times (indexes) when an event (inv, res pair) pair occurs in a history
EventTimes(H, e) == 
    LET inv == e[1]
        res == e[2]
    IN {<<i,j>> \in OpTimes(H,inv) \X OpTimes(H,res) : Matches(H, i, j)}

\* operation e1 precedes operation e2 if the response of e1 happens before
\* the invocation of e2
\* Operations are pairs (tuples) of events << inv, res >>
Precedes(H, e1, e2) == 
    \E t1 \in EventTimes(H, e1) : \E t2 \in EventTimes(H,e2) : t1[2] < t2[1]

\* Operations are pairs (tuples) of events << inv, res >>
Operations(H) == 
    LET N == Len(H)
        ts == {<<i,j>> \in (1..N) \X (1..N) : Matches(H,i,j)}
    IN {<<H[t[1]], H[t[2]]>> : t \in ts}

\* True if <_H ⊆ <_S
\*
\* A history H induces an irreflexive partial order < H on operations:
\* e0 <_H e1 if res(e0) precedes inv(e1) in H
RespectsPrecedenceOrdering(H, S) == 
    LET LTH(x, y) == Precedes(H, x, y)
        LTS(x, y) == Precedes(S, x, y)
        ops == Operations(H) \union Operations(S)
        Pairs(h, LT(_, _)) == {e \in ops \X ops: LT(e[1], e[2]) }
    IN Pairs(H, LTH) \subseteq Pairs(S, LTS)


\* TRUE if history contains only invocations and matching responses
OnlyInvAndMatchingResponses(H) == InvocationsWithoutResponses(H) = {} 

\* If H is a history, complete(H) is the maximal subsequence of H consisting only
\* of invocations and matching responses.
Complete(H) ==
    LET subseqs == Subsequences(H)
    IN CHOOSE CH \in subseqs :
        /\ OnlyInvAndMatchingResponses(CH) 
        /\ \A s \in subseqs : OnlyInvAndMatchingResponses(s) => Len(s) <= Len(CH) \* maximal

\* A history H is sequential if:
\* 1. The first event of H is an invocation.
\* 2. Each invocation, except possibly the last, is immediately followed by a
\*    matching response. Each response is immediately followed by a matching
\*    invocation.
IsSequential(H) ==
    LET IsLastInvocation(h,i) == \A j \in 1..Len(h) : IsInvocation(h[j]) => j<=i
    IN /\ Len(H)>0 => IsInvocation(H[1])
       /\ \A i \in 1..Len(H) : IsInvocation(H[i]) => (IsLastInvocation(H,i) \/ Matches(H, i, i+1))
       /\ \A i \in 1..Len(H) : IsResponse(H[i]) => Matches(H,i-1,i)

(***************************************************************************

Herlihy & Wing 1990, p469:

A history H is linearizable if it can be extended (by appending zero or more
response events) to some history H’ such that:

L1: complete(H’) is equivalent to some legal sequential history S, and
L2: <_H ⊆ <_S

Two histories H and H’ are equivalent if for every process P, H|P = H’|P.

If H is a history, complete(H) is the maximal subsequence of H consisting only
of invocations and matching responses.

***************************************************************************)

IsLinearizableHistory(H) == 
    \E Hp \in ExtendedHistories(H) : 
       LET completeHp == Complete(Hp)
       IN \E f \in Orderings(Len(completeHp)) :
            LET S == completeHp ** f
            IN /\ IsSequential(S)
               /\ IsLegal(S)
               /\ AreEquivalent(S, completeHp)
               /\ RespectsPrecedenceOrdering(H, S)
                
Linearize(H) ==
    LET Hp == CHOOSE Hp \in ExtendedHistories(H) : 
       LET completeHp == Complete(Hp)
       IN \E f \in Orderings(Len(completeHp)) :
            LET S == completeHp ** f
            IN /\ IsSequential(S)
               /\ IsLegal(S)
               /\ AreEquivalent(S, completeHp)
               /\ RespectsPrecedenceOrdering(H, S)
       completeHp == Complete(Hp)
       f == CHOOSE f \in Orderings(Len(completeHp)) :
            LET S == completeHp ** f
            IN /\ IsSequential(S)
               /\ IsLegal(S)
               /\ AreEquivalent(S, completeHp)
               /\ RespectsPrecedenceOrdering(H, S)
    IN Hp**f
=============================================================================
\* Modification History
\* Last modified Tue Oct 23 18:49:20 PDT 2018 by lhochstein
\* Created Sat Oct 20 09:56:44 PDT 2018 by lhochstein
