---- MODULE lockserver_nodefs ----
EXTENDS TLC, Naturals
\*
\* Simple lock server example. (version with all definitions expanded.)
\*
\* The system consists of a set of servers and a set of clients. Each server
\* maintains a single lock, which can be granted to a client if it currently
\* owns that lock. 
\* 

\* Hard-code constants inline for now.
\* CONSTANT Server = {0,1,2}
\* CONSTANT Client = {88,99}

VARIABLE semaphore
VARIABLE clientlocks

\* Initially each server holds its lock, and all clients hold no locks.
Init == 
    /\ semaphore = [i \in {0,1,2} |-> TRUE]
    /\ clientlocks = [i \in {88,99} |-> {}]

Next == 
    \* Connect(c,s)
    \* A client c requests a lock from server s.
    \/ \E c \in {88,99}, s \in {0,1,2} : 
        \* The server must currently hold the lock.
        /\ semaphore[s] = TRUE
        \* The client obtains the lock of s.
        /\ clientlocks' = [clientlocks EXCEPT ![c] = clientlocks[c] \cup {s}]
        /\ semaphore' = [semaphore EXCEPT ![s] = FALSE]
    \* Disconnect(c,s)
    \* A client c relinquishes the lock of server s.
    \/ \E c \in {88,99}, s \in {0,1,2} : 
        \* The client must currently be holding the lock of s.
        /\ s \in clientlocks[c]
        \* The client relinquishes the lock of s.
        /\ clientlocks' = [clientlocks EXCEPT ![c] = clientlocks[c] \ {s}]
        /\ semaphore' = [semaphore EXCEPT ![s] = TRUE]

\* TypeOK == 
    \* /\ semaphore \in [Server -> BOOLEAN]
    \* /\ clientlocks \in [Client -> SUBSET Server]

\* Two different clients cannot hold the lock of the same server simultaneously.
\* Inv == \A ci,cj \in Client : (clientlocks[ci] \cap clientlocks[cj] # {}) => (ci = cj)

====