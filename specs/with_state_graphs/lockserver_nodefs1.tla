---- MODULE lockserver_nodefs1 ----
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
\* CONSTANT Client = {"c1","c2"}

Server == {"s1", "s2"}
Client == {"c1", "c2"}

VARIABLE semaphore
VARIABLE clientlocks

\* Initially each server holds its lock, and all clients hold no locks.
Init == 
    /\ semaphore = [s1 |-> FALSE, s2 |-> TRUE]
    /\ clientlocks = [c1 |-> {}, c2 |-> {"s1"}]

Next == 
    \* \/ \E c \in Client, s \in Server : 
    \*     /\ semaphore[s] = TRUE
    \*     /\ clientlocks' = [clientlocks EXCEPT ![c] = clientlocks[c] \cup {s}]
    \*     /\ semaphore' = [semaphore EXCEPT ![s] = FALSE]
    \* Disconnect.
    \E c \in Client, s \in Server : 
        /\ s \in clientlocks[c]
        /\ clientlocks' = [clientlocks EXCEPT ![c] = clientlocks[c] \ {s}]
        /\ semaphore' = [semaphore EXCEPT ![s] = TRUE]

====