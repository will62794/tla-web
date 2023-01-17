------------------------------- MODULE MultiPaxos -------------------------------
(***************************************************************************)
(* This is a TLA+ specification and machine checked proof of the           *)
(* MultiPaxos Consensus algorithm.                                         *)
(***************************************************************************)
EXTENDS Integers

CONSTANT Ballots, Slots
CONSTANTS Acceptors, Values, Quorums, Proposers

ASSUME QuorumAssumption == Quorums \subseteq SUBSET Acceptors /\ \A Q1, Q2 \in Quorums: Q1 \cap Q2 # {}

VARIABLES msgs     \* Set of sent messages
VARIABLE aVoted    \* Set of <<ballot, slot, value>> triples per acceptor that it has VotedForIn.
VARIABLE aBal      \* For each acceptor, the highest ballot seen by it.
VARIABLE pBal      \* Current ballot being run by proposers

vars == <<msgs, aVoted, aBal, pBal>>

Send(m) == msgs' = msgs \cup {m}

(***************************************************************************)
(* Phase 1a: Executed by a proposer, it selects a ballot number on which   *)
(* Phase 1a has never been initiated. This number is sent to any set of    *)
(* acceptors which contains at least one quorum from Quorums. Trivially it *)
(* can be broadcasted to all Acceptors. For safety, any subset of          *)
(* Acceptors would suffice. For liveness, a subset containing at least one *)
(* Quorum is needed.                                                       *)
(***************************************************************************)
Phase1a(p) == \E b \in Ballots:
                /\ pBal' = [pBal EXCEPT![p] = b]
                /\ Send([type |-> "1a", from |-> p, bal |-> b])
                /\ UNCHANGED <<aVoted, aBal>>
              
(***************************************************************************)
(* Phase 1b: If an acceptor receives a 1a message with ballot b greater    *)
(* than that of any 1a message to which it has already responded, then it  *)
(* responds to the request with a promise not to accept any more proposals *)
(* for ballots numbered less than b; otherwise it sends a preempt to the   *)
(* proposer telling the greater ballot.                                    *)
(* In case of a 1b reply, the acceptor writes a mapping in Slots ->        *)
(* Ballots \times Values. This mapping reveals for each slot, the value    *)
(* that the acceptor most recently (that is, highest ballot) voted on, if  *)
(* any.                                                                    *)
(***************************************************************************)
Phase1b(a) == \E m \in msgs:
                /\ m.type = "1a"
                /\ m.bal > aBal[a]
                /\ Send([type |-> "1b", from |-> a, bal |-> m.bal, voted |-> aVoted[a]])
                /\ aBal' = [aBal EXCEPT ![a] = m.bal]
                /\ UNCHANGED <<aVoted, pBal>>
        
(***************************************************************************)
(* Phase 2a: If the proposer receives a response to its 1b message (for    *)
(* ballot b) from a quorum of acceptors, then it sends a 2a message to all *)
(* acceptors for a proposal in ballot b. Per slot received in the replies, *)
(* the proposer finds out the value most recently (i.e., highest ballot)   *)
(* voted by the acceptors in the received set. Thus a mapping in Slots ->  *)
(* Values is created. This mapping along with the ballot that passed Phase *)
(* 1a is propogated to again, any subset of Acceptors - Hopefully to one   *)
(* containing at least one quorum. Bmax creates the desired mapping from   *)
(* received replies. NewProposals instructs how new slots are entered in   *)
(* the system.                                                             *)
(***************************************************************************)
PartialBmax(T)    == {t \in T: \A t1 \in T: t1.slot = t.slot => t1.bal \leq t.bal}
Bmax(T)           == {[slot |-> t.slot, val |-> t.val]: t \in PartialBmax(T)}
FreeSlots(T)      == {s \in Slots: ~\E t\in T: t.slot = s}
NewProposals(T)   == CHOOSE D \in SUBSET [slot: FreeSlots(T), val: Values]:
                       \A d1, d2 \in D: d1.slot = d2.slot => d1 = d2
ProposeDecrees(T) == Bmax(T) \cup NewProposals(T)




Phase2a(p) ==
  /\ ~\E m \in msgs: (m.type = "2a") /\ (m.bal = pBal[p])
  /\ \E Q \in Quorums, S \in SUBSET {m \in msgs: (m.type = "1b") /\ (m.bal = pBal[p])}:
       /\ \A a \in Q: \E m \in S: m.from = a
       /\ Send([type |-> "2a", from |-> p, bal |-> pBal[p], decrees |-> ProposeDecrees(UNION {m.voted: m \in S})])
  /\ UNCHANGED <<aBal, aVoted, pBal>>

(***************************************************************************)
(* Phase 2b: If an acceptor receives a 2a message for a ballot which is    *)
(* the highest that it has seen, it votes for the all the message's values *)
(* in ballot b.                                                            *)
(***************************************************************************)
Phase2b(a) == \E m \in msgs:
                /\ m.type = "2a"
                /\ m.bal \geq aBal[a]
                /\ Send([type |-> "2b", from |-> a, bal |-> m.bal, decrees |-> m.decrees])
                /\ aBal' = [aBal EXCEPT ![a] = m.bal]
                /\ aVoted' = [aVoted EXCEPT ![a] = {d \in aVoted[a]: ~\E d2 \in m.decrees: d.slot = d2.slot } \cup
                               {[bal |-> m.bal, slot |-> d.slot, val |-> d.val]: d \in m.decrees}]
                /\ UNCHANGED <<pBal>>

Init == 
    /\ aVoted = [a \in Acceptors |-> {}]  
    /\ msgs = {} 
    /\ aBal = [a \in Acceptors |-> -1]  
    /\ pBal = [p \in Proposers |-> 0]

Next == 
    \/ \E p \in Proposers: Phase1a(p)
    \/ \E p \in Proposers: Phase2a(p)
    \/ \E a \in Acceptors: Phase1b(a)
    \/ \E a \in Acceptors: Phase2b(a)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

(***************************************************************************)
(* How a value is chosen:                                                  *)
(*                                                                         *)
(* This spec does not contain any actions in which a value is explicitly   *)
(* chosen (or a chosen value learned).  What it means for a value to be    *)
(* chosen is defined by the operator Chosen, where Chosen(s, v) means that *)
(* value v has been chosen for slot s.                                     *)
(***************************************************************************)
VotedForIn(a, b, s, v) == \E m \in msgs:
  m.type = "2b" /\ m.from = a /\ m.bal = b /\ \E d \in m.decrees: d.slot = s /\ d.val = v

ChosenIn(b, s, v) == \E Q \in Quorums: \A a \in Q: VotedForIn(a, b, s, v)
Chosen(s, v) == \E b \in Ballots: ChosenIn(b, s, v)

(***************************************************************************)
(* The consistency condition that a consensus algorithm must satisfy is    *)
(* the invariance of the following state predicate Consistency.            *)
(***************************************************************************)
Consistency == \A v1, v2 \in Values, s \in Slots: Chosen(s, v1) /\ Chosen(s, v2) => (v1 = v2)
-----------------------------------------------------------------------------



(***************************************************************************)
(* This section of the spec defines the invariant Inv.                     *)
(***************************************************************************)
Messages == [type: {"1a"}, from: Proposers, bal: Ballots] \cup
            [type: {"1b"}, from: Acceptors, bal: Ballots, voted: SUBSET [bal: Ballots, slot: Slots, val: Values]] \cup
            [type: {"2a"}, from: Proposers, bal: Ballots, decrees: SUBSET [slot: Slots, val: Values]] \cup
            [type: {"2b"}, from: Acceptors, bal: Ballots, decrees: SUBSET [slot: Slots, val: Values]] \cup
            [type: {"preempt"}, to: Proposers, bal: Ballots]

TypeOK == /\ msgs \in SUBSET Messages /\ aVoted \in [Acceptors -> SUBSET [bal: Ballots, slot: Slots, val: Values]]
          /\ aBal \in [Acceptors -> Ballots \cup {-1}] /\ pBal \in [Proposers -> Ballots]

(***************************************************************************)
(* WontVoteIn(a, b, s) is a predicate that implies that acceptor a has not *)
(* voted and will never vote in ballot b wrt slot s.                       *)
(***************************************************************************)                                       
WontVoteIn(a, b, s) == aBal[a] > b /\ \A v \in Values: ~ VotedForIn(a, b, s, v)

(***************************************************************************)
(* The predicate SafeAt(b, s, v) implies that no value other than perhaps  *)
(* v has been or ever will be chosen in any ballot numbered less than b    *)
(* for slot s.                                                             *)
(***************************************************************************)                   
SafeAt(b, s, v) == \A b2 \in 0..(b-1): \E Q \in Quorums: \A a \in Q: VotedForIn(a, b2, s, v) \/ WontVoteIn(a, b2, s)

(***************************************************************************)
(* Max(S) picks the largest element in the set S.                          *)
(***************************************************************************)
Max(S) == CHOOSE b \in S: \A b2 \in S: b \geq b2

(***************************************************************************)
(* MaxBallotInSlot(S, s) picks the highest ballot in S for slot s or       *)
(* -1 if S has no vote in slot s. S is a set of records with at least two  *)
(* fields: slot and bal.                                                   *)
(***************************************************************************)
MaxBallotInSlot(S, s) == LET B == {e.bal: e \in {e \in S: e.slot = s}}  IN
                         IF {e \in S: e.slot = s} = {} THEN -1 ELSE Max(B)

MsgInv1b(m) == /\ m.bal \leq aBal[m.from]
               /\ \A r\in m.voted: VotedForIn(m.from, r.bal, r.slot, r.val)
               /\ \A b2\in Ballots, s\in Slots, v \in Values: b2 \in MaxBallotInSlot(m.voted, s)+1..m.bal-1 =>
                      ~ VotedForIn(m.from, b2, s, v)

MsgInv2a(m) == /\ \A d \in m.decrees: SafeAt(m.bal, d.slot, d.val)
               /\ \A d1,d2 \in m.decrees: d1.slot = d2.slot => d1 = d2
               /\ \A m2 \in msgs: (m2.type = "2a" /\ m2.bal = m.bal) => m = m2

MsgInv2b(m) == /\ \E m2 \in msgs: m2.type = "2a" /\ m2.bal = m.bal /\ m2.decrees = m.decrees
               /\ m.bal \leq aBal[m.from]

MsgInv == \A m \in msgs: /\ (m.type = "1b") => MsgInv1b(m)
                         /\ (m.type = "2a") => MsgInv2a(m)
                         /\ (m.type = "2b") => MsgInv2b(m)

AccInv == \A a \in Acceptors:
  /\ aBal[a] = -1 => aVoted[a] = {}
  /\ \A r \in aVoted[a]: aBal[a] \geq r.bal /\ VotedForIn(a, r.bal, r.slot, r.val)
  /\ \A b \in Ballots, s \in Slots, v \in Values: VotedForIn(a, b, s, v) => \E r \in aVoted[a]: r.bal \geq b /\ r.slot = s
  /\ \A b \in Ballots, s \in Slots, v \in Values: b > MaxBallotInSlot(aVoted[a], s) => ~ VotedForIn(a, b, s, v)

P1 == ~(\E m \in msgs : m.type = "2b")
P2 == ~(\E a \in Acceptors : aVoted[a] # {})

=============