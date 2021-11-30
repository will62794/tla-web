---- MODULE lockserver ----
EXTENDS TLC, Naturals

\*
\* Simple lock server example.
\*
\* The system consists of a set of servers and a set of clients.
\* Each server maintains a single lock, which can be granted to a 
\* client if it currently owns that lock. 
\* 

CONSTANT Server,Client

CONSTANT Nil

VARIABLE semaphore
VARIABLE clientlocks

\* A client c requests a lock from server s.
Connect(c, s) == 
    \* The server must currently hold the lock.
    /\ semaphore[s] = TRUE
    \* The client obtains the lock of s.
    /\ clientlocks' = [clientlocks EXCEPT ![c] = clientlocks[c] \cup {s}]
    /\ semaphore' = [semaphore EXCEPT ![s] = FALSE]


\* A client c relinquishes the lock of server s.
Disconnect(c, s) ==
    \* The client must currently be holding the lock of s.
    /\ s \in clientlocks[c]
    \* The relinquishes the lock of s.
    /\ clientlocks' = [clientlocks EXCEPT ![c] = clientlocks[c] \ {s}]
    /\ semaphore' = [semaphore EXCEPT ![s] = TRUE]
    
Init == 
    \* Initially each server holds its lock, and all clients hold 
    \* no locks.
    /\ semaphore = [i \in Server |-> TRUE]
    /\ clientlocks = [i \in Client |-> {}]

Next == 
    \/ \E c \in Client, s \in Server : Connect(c, s)
    \/ \E c \in Client, s \in Server : Disconnect(c, s)

TypeOK == 
    /\ semaphore \in [Server -> BOOLEAN]
    /\ clientlocks \in [Client -> SUBSET Server]

\* Two different clients cannot hold the lock of the same server simultaneously.
Inv == \A ci,cj \in Client : (clientlocks[ci] \cap clientlocks[cj] # {}) => (ci = cj)

\* The inductive invariant.
Ind == 
    /\ TypeOK
    /\ Inv
    \* A client and server never hold the same lock at the same time.
    /\ \A c \in Client, s \in Server : (s \in clientlocks[c]) => ~semaphore[s]

====