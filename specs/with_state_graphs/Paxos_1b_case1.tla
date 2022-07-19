-------------------------------- MODULE Paxos_1b_case1 -------------------------------
(***************************************************************************)
(* This is a specification of the Paxos algorithm.                         *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

\* Hard-coded constants for now.
Acceptor == {"a1", "a2"}
Quorum == {{"a1", "a2"}}
Proposer == {"p1", "p2"}
Value == {"v1", "v2"}
Ballot == {0,1}   
None == "None"  

ASSUME QuorumAssumption == /\ \A Q \in Quorum : Q \subseteq Acceptor
                           /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {} 
      

VARIABLE maxBal 
VARIABLE maxVBal \* <<maxVBal[a], maxVal[a]>> is the vote with the largest
VARIABLE maxVal    \* ballot number cast by a; it equals <<-1, None>> if a has not cast any vote.
VARIABLE msgs     \* The set of all messages that have been sent.

(***************************************************************************)
(* NOTE:                                                                   *)
(* The algorithm is easier to understand in terms of the set msgs of all   *)
(* messages that have ever been sent.  A more accurate model would use     *)
(* one or more variables to represent the messages actually in transit,    *)
(* and it would include actions representing message loss and duplication  *)
(* as well as message receipt.                                             *)
(*                                                                         *)
(* In the current spec, there is no need to model message loss because we  *)
(* are mainly concerned with the algorithm's safety property.  The safety  *)
(* part of the spec says only what messages may be received and does not   *)
(* assert that any message actually is received.  Thus, there is no        *)
(* difference between a lost message and one that is never received.  The  *)
(* liveness property of the spec that we check makes it clear what what    *)
(* messages must be received (and hence either not lost or successfully    *)
(* retransmitted if lost) to guarantee progress.                           *)
(***************************************************************************)

vars == <<maxBal, maxVBal, maxVal, msgs>>
  
Init == 
    /\ maxBal = [a1 |-> -1, a2 |-> -1]
    /\ maxVBal = [a1 |-> -1, a2 |-> -1]
    /\ maxVal = [a1 |-> "None", a2 |-> "None"]
    /\ msgs = {[type |-> "1a", bal |-> 1, proposer |-> "p1"]}

Send(m) == msgs' = msgs \cup {m}

(***************************************************************************)
(* Upon receipt of a ballot b phase 1a message, acceptor a can perform a   *)
(* Phase1b(a) action only if b > maxBal[a].  The action sets maxBal[a] to  *)
(* b and sends a phase 1b message to the leader containing the values of   *)
(* maxVBal[a] and maxVal[a].                                               *)
(***************************************************************************)
Phase1b(a, p) == 
    \E m \in msgs :
        /\ m.proposer = p
        /\ m.type = "1a"
        /\ m.bal >= maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ msgs' = msgs \cup {[type |-> "1b", acc |-> a, bal |-> m.bal, mbal |-> maxVBal[a], mval |-> maxVal[a], proposer |-> p]}
        /\ maxVBal' = maxVBal
        /\ maxVal'  = maxVal

Next == 
    \/ \E a \in Acceptor : \E p \in Proposer : Phase1b(a, p) 

Spec == Init /\ [][Next]_vars

============================================================================