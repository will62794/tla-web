----------------------- MODULE simple_seq_ext ------------------------
EXTENDS Sequences,TLC, Naturals, SequencesExt, FiniteSets
VARIABLE x
Init == 
    \/ x = SelectLastInSeq(<<1,2,3,4,5,2,1,1>>, LAMBDA v : v > 2)
    \/ x = SelectLastInSeq(<<{1,2,3}, {1,2}, {2,3}, {3,4,5}>>, LAMBDA v : Cardinality(v) = 2)
Next == x' = x
====