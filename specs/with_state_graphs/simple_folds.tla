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

FoldLeft(opA(_, _), baseArg, seqArg) == 
  MapThenFoldSet(LAMBDA x,y : opA(y,x), baseArg,
                 LAMBDA i : seqArg[i],
                 LAMBDA S : Max(S),
                 DOMAIN seqArg)


VARIABLE
    seq,
    val

Init ==
    \/ /\ seq = << 1, 2, 3 >>
       /\ val = FoldLeft(LAMBDA x, y: x + y, 0, seq)
    \/ /\ seq = << 2, 5, 6 >>
       /\ val = FoldLeft(LAMBDA x, y: x + y, 0, seq)
    \/ /\ seq = << 1, 1, 9 >>
       /\ val = FoldLeft(LAMBDA x, y: x + y, 2, seq)

Next == UNCHANGED << seq, val >>
   
====