----------------------------- MODULE Utilities -----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* Composition
f ** g == [x \in DOMAIN(g) |-> f[g[x]]]

\* Pick a subsequence of S that matches the set of indices, inds
Subseq(S, inds) ==
    LET F[i \in 0..Len(S)] ==
        IF i = 0 THEN << >>
        ELSE IF i \in inds THEN Append(F[i-1], S[i])
             ELSE F[i-1]
    IN F[Len(S)]

\* All subssequences of S
\*
\* A subsequence is a sequence that can be derived from another sequence by deleting
\* some or no elements without changing the order of the remaining elements (Wikipedia).
Subsequences(S) ==  {Subseq(S,inds) : inds \in SUBSET(1..Len(S))} 

\* Given a set, return a sequence made of its elements
RECURSIVE ToSeq(_)
ToSeq(S) == IF S = {} THEN << >>
            ELSE LET e == CHOOSE e \in S : TRUE
                     T == S \ {e}
                 IN Append(ToSeq(T), e)

\* Returns a set of functions on 1..N->1..N that represent permutations
\* for reordering a sequence of events
\*
\* This is a simple implementation that filters down from a larger set.
OrderingsSimple(N) == LET S == 1..N
                    Range(f) == { f[x] : x \in DOMAIN f }
                    Onto(f) == DOMAIN f = Range(f)
                IN {f \in [S->S] : Onto(f)}

\* Returns a set of functions on 1..N->1..N that represent permutations
\* for reordering a sequence of events
\*
\* This constructs the set rather than filtering down.
\*
RECURSIVE Orderings(_)
Orderings(N) == 
    CASE N=0 -> {}
      [] N=1 -> {[x \in {1}|->1]}
      [] OTHER -> LET fs == Orderings(N-1)
                      Helper(n, fp) == LET f == Append(fp,n) IN {[f EXCEPT ![x]=f[n], ![n]=f[x]] : x \in 1..n }
                  IN UNION({Helper(N,f): f \in fs})

\* Given a set, return a set of sequences that are permutations 
Perms(S) == LET fs == Orderings(Cardinality(S))
                s == ToSeq(S)
            IN {s**f: f \in fs}


=============================================================================
\* Modification History
\* Last modified Tue Oct 23 18:40:06 PDT 2018 by lhochstein
\* Created Mon Oct 22 19:21:10 PDT 2018 by lhochstein
