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
    \/ \E c \in {88,99}, s \in {0,1,2} : 
        /\ semaphore[s] = TRUE
        /\ clientlocks' = [clientlocks EXCEPT ![c] = clientlocks[c] \cup {s}]
        /\ semaphore' = [semaphore EXCEPT ![s] = FALSE]
    \/ \E c \in {88,99}, s \in {0,1,2} : 
        /\ s \in clientlocks[c]
        /\ clientlocks' = [clientlocks EXCEPT ![c] = clientlocks[c] \ {s}]
        /\ semaphore' = [semaphore EXCEPT ![s] = TRUE]

====