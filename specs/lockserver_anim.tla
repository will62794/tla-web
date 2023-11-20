---- MODULE lockserver_anim ----

EXTENDS TLC, Naturals, FiniteSets

\*
\* Simple lock server example.
\*
\* The system consists of a set of servers and a set of clients.
\* Each server maintains a single lock, which can be granted to a 
\* client if it currently owns that lock. 
\* 

CONSTANT Server,Client

VARIABLE semaphore
VARIABLE clientlocks

vars == <<semaphore, clientlocks>>

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

NextUnchanged == UNCHANGED vars

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

\* Group element. 'children' is as a sequence of elements that will be contained in this group.
Group(children, attrs) == SVGElem("g", attrs, children)

Injective(f) == \A x, y \in DOMAIN f : f[x] = f[y] => x = y

\* Establish a fixed mapping to assign an ordering to elements in these sets.
\* ServerId == CHOOSE f \in [Server -> 1..Cardinality(Person)] : Injective(f)
ServerId == CHOOSE f \in [1..2 -> {"s1","s2"}] : Injective(f)

\* Animation view definition.
c1 == Circle(10, 10, 3, [fill |-> "red"])
c2 == Circle(20, 10, 3, [fill |-> "red"])
\* ServerIdDomain == 1..Cardinality(Server)
ServerIdDomain == 1..2
cs == [i \in ServerIdDomain |-> Circle(20 * i, 10, 3, [fill |-> IF semaphore[ServerId[i]] THEN "green" ELSE "orange"])]
        \* ServerId[i] ]
\* ctest == [i \in {1,2} |-> Circle(i*15, 10, 3, [fill |-> "red"])]
AnimView == Group(cs, [i \in {} |-> {}])

====
