----------------------- MODULE simple_fcn_polymorphism ------------------------
EXTENDS Sequences, Naturals

\* Test the ability to handle functions/records/tuples interchangeably.

VARIABLE x

seq == <<1, 2, 3>>

Init == x = [
    f1 |-> DOMAIN <<1,2,3>>,
    f2 |-> Append([i \in {1, 2, 3} |-> 0], 5),
    f3 |-> [ i \in DOMAIN seq |->
            IF i = 1 THEN
                IF seq[1] = 5 THEN 1 ELSE seq[1] + 1
            ELSE seq[i]],
    f4 |-> [seq EXCEPT ![1] = IF @ = 5 THEN 1 ELSE @ + 1],
    f5 |-> Append([seq EXCEPT ![1] = IF @ = 5 THEN 1 ELSE @ + 1], 7),
    f6 |-> Tail([i \in {1, 2, 3} |-> 0]),
    f7 |-> Head([i \in {1, 2, 3} |-> 0]),
    f8 |-> Len([i \in {1, 2, 3, 4} |-> 0]),
    f9 |->  <<0, 0, 0>> = [i \in {1, 2, 3} |-> 0],
    f10 |->  <<0, 0, 1>> = [i \in {1, 2, 3} |-> 0]
]
Next == x' = x
====