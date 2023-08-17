---- MODULE repl ----
\*
\* Simple REPL scratchpad.
\*

IsInjective(f) == \A a,b \in DOMAIN f : f[a] = f[b] => a = b

SeqOf(set, n) == 
  (***************************************************************************)
  (* All sequences up to length n with all elements in set.  Includes empty  *)
  (* sequence.                                                               *)
  (***************************************************************************)
  UNION {[1..m -> set] : m \in 0..n}

SetToSeq(S) == 
  (**************************************************************************)
  (* Convert a set to some sequence that contains all the elements of the   *)
  (* set exactly once, and contains no other elements.                      *)
  (**************************************************************************)
  CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)

Add(x, y) == x + y

M == {1,2,3}

====