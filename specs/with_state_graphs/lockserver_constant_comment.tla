---- MODULE lockserver_constant_comment ----
EXTENDS TLC, Naturals
\*
\* Simple lock server example. (version with all definitions expanded.)
\*
\* The system consists of a set of servers and a set of clients. Each server
\* maintains a single lock, which can be granted to a client if it currently
\* owns that lock. 
\* 

(***************************************************************************)
(* This specification describes a protocol                                 *)
(* This specification describes a protocol                                 *)
(* This specification describes a protocol                                 *)
(* This specification describes a protocol                                 *)
(***************************************************************************)

\* Hard-code constants inline for now.
CONSTANT Server, (**)
         Client 
\* CONSTANT Client

\* Server == {"s1", "s2"}
\* Client == {"c1", "c2"}

VARIABLE semaphore
VARIABLE clientlocks

TypeOK ==
    (*
        block comment.
    *)
    /\ semaphore \in [Server -> {TRUE, FALSE}]
    /\ clientlocks \in [Client -> SUBSET Server]

\* Initially each server holds its lock, and all clients hold no locks.
Init == 
    /\ semaphore = [i \in Server |-> TRUE]
    /\ clientlocks = [i \in Client |-> {}]

Next == 
    \/ \E c \in Client, s \in Server : 
        /\ semaphore[s] = TRUE
        /\ clientlocks' = [clientlocks EXCEPT ![c] = clientlocks[c] \cup {s}]
        /\ semaphore' = [semaphore EXCEPT ![s] = FALSE]
    \/ \E c \in Client, s \in Server : 
        /\ s \in clientlocks[c]
        /\ clientlocks' = [clientlocks EXCEPT ![c] = clientlocks[c] \ {s}]
        /\ semaphore' = [semaphore EXCEPT ![s] = TRUE]

====