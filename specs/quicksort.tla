---- MODULE quicksort ----
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

\*
\* Specification of Quicksort in TLA+.
\*

\* The sequence of numbers to be sorted.
VARIABLE seq

\* The set of intervals that have yet to be sorted.
VARIABLE intervals

vars == <<seq, intervals>>

CONSTANT MaxSeqLen

SeqOf(set, n) == UNION {[1..m -> set] : m \in 0..n}
BoundedSeq(S) == SeqOf(S, MaxSeqLen)

IsInjective(f) == \A a,b \in DOMAIN f : f[a] = f[b] => a = b
SetToSeq(S) == 
  (**************************************************************************)
  (* Convert a set to some sequence that contains all the elements of the   *)
  (* set exactly once, and contains no other elements.                      *)
  (**************************************************************************)
  CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)

\* For given interval (i,j), and a pivot p, move all elements <= p to left of p
\* and all those > p to the right.

\* Given sequence 's' and pivot index 'p', return a sequence such that 
\* rearrange the sequence so that all values <= s[p] are moved to the left of 
\* index p and all values > p are moved to an index to the right of p.
Partition(s, p) == 
    \* Construct the left/right partitions.
    LET leq(v) == v <= s[p]
        gt(v) == v > s[p]
        lPart == SelectSeq(s, leq)
        rPart == SelectSeq(s, gt) IN 
    \* Reconstruct the partitioned sequence.
    lPart \o <<s[p]>> \o rPart
        
\* <<1,5,3,4,4,2,1,4>>
\* {<<1,8>>}
\* 1. choose an interval I from the set of unsorted intervals.
\* 2. Choose a pivot in I, which is a random index within the bounds of I.
\* 3. Move all elements < pivot to its left and those > pivot to its right.
\* 4. Add the intervals (I.low,pivot) and (pivot,high) to the set of intervals.

\* TODO.
\* Choose a permutation of the indices in the interval such that they move all lesser values
\* left of p and same for greater values


\* Partition interval given by <<lo,hi>> with pivot index p.
PartitionInterval(lo, hi, p) == 
    \E f \in Permutations(lo..hi) : 
        /\ f[p] = p \* the pivot doesn't move.
        /\ \A i \in lo..hi :
            /\ f[i] < p => (seq[i] <= seq[p])
            /\ f[i] > p => (seq[i] > seq[p])
        /\ seq' = [j \in 1..Len(seq) |-> 
                    IF j \in lo..hi 
                    THEN seq[f[j]] 
                    ELSE seq[j]]
        \* Remove the original interval and add its sub intervals.
        \* Don't add any new intervals if the interval is empty i.e. lo = hi.
        /\ LET newIntervals == IF lo = hi THEN {} ELSE {<<lo,(p-1)>>, <<p,hi>>} IN
               intervals' = (intervals \ {<<lo,hi>>}) \cup newIntervals
            
Init == 
    \* Assume non-empty sequences.
    \*/\ seq \in Seq(Nat) /\ seq # <<>>
    /\ seq = <<1,8,3,1,4,15,6,4>>
    /\ intervals = {<<1,Len(seq)>>}

Next == 
    \E <<lo,hi>> \in intervals:
    \E p \in lo..hi :
        \/ PartitionInterval(lo, hi, p)

Liveness == WF_vars(Next)
    
Spec == Init /\ [][Next]_<<seq,intervals>> /\ Liveness

\* Is the sequence 's' sorted.
Sorted(s) == \A i \in 1..(Len(s)-1) : seq[i] <= seq[i+1]

\* If the set of intervals is empty, then the sequence must be sorted.
PartialCorrectness == (intervals = {}) => Sorted(seq)

\* Does the algorithm always terminate?
Termination == <>(intervals = {})

====