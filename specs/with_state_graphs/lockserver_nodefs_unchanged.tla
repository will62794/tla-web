---- MODULE lockserver_nodefs_unchanged ----
EXTENDS TLC, Naturals

Server == {"s1", "s2"}
Client == {"c1", "c2"}

VARIABLE semaphore
VARIABLE clientlocks
vars==<<semaphore, clientlocks>>

TypeOK ==
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
    \/ UNCHANGED vars

====