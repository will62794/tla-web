---- MODULE simple_folds ----
EXTENDS Naturals

Max(s) == CHOOSE x \in s : \A y \in s : x >= y

\* The following two definitions are copied verbatim from the community modules
MapThenFoldSet(op(_,_), base, f(_), choose(_), S) ==
  LET iter[s \in SUBSET S] ==
        IF s = {} THEN base
        ELSE LET x == choose(s)
             IN  op(f(x), iter[s \ {x}])
  IN  iter[S]

FoldLeft(op(_, _), base, seq) == 
  MapThenFoldSet(LAMBDA x,y : op(y,x), base,
                 LAMBDA i : seq[i],
                 LAMBDA S : Max(S),
                 DOMAIN seq)


VARIABLE
    seq,
    val

Init ==
    /\ seq = << 1, 2, 3 >>
    /\ val = FoldLeft(LAMBDA x, y: x + y, 0, seq)

Next == UNCHANGED << seq, val >>
   
====