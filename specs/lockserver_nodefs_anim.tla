---- MODULE lockserver_nodefs_anim ----
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


------------------------------------------------------------
\* 
\* Animation stuff.
\* 

\* Merge two records
Merge(r1, r2) == 
    LET D1 == DOMAIN r1 D2 == DOMAIN r2 IN
    [k \in (D1 \cup D2) |-> IF k \in D1 THEN r1[k] ELSE r2[k]]

SVGElem(_name, _attrs, _children) == [name |-> _name, attrs |-> _attrs, children |-> _children ]

\* Circle element. 'cx', 'cy', and 'r' should be given as integers.
Circle(cx, cy, r, attrs) == 
    LET svgAttrs == [cx |-> cx, 
                     cy |-> cy, 
                     r  |-> r] IN
    SVGElem("circle", Merge(svgAttrs, attrs), <<>>)


\* Animation view definition.
View == Circle(10, 10, 3, [fill |-> "red"])

====