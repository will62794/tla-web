---- MODULE simple_lockserver_with_constants ----
VARIABLE semaphore
VARIABLE clientlocks

CONSTANT Server
CONSTANT Client

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