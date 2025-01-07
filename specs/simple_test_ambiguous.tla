---------------------- MODULE simple_test_ambiguous -------------------------
EXTENDS Naturals
VARIABLES count
Init == count = 0
Incr(N) == count' = count + N
Next == Incr(1) \/ Incr(2)
Spec == Init /\ [][Next]_count
============================================================