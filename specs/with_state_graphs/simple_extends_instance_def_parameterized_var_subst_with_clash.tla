---- MODULE simple_extends_instance_def_parameterized_var_subst_with_clash ----
EXTENDS Sequences, Naturals

D == {"a","b"}
VARIABLES x

M(c) == INSTANCE simple_extends_M8 WITH x <- x[c]

Init == 
    \/ /\ x \in [D -> 0..2]
       /\ M("a")!XCond
    \/ /\ x \in [D -> 0..2]
       /\ M("b")!XCond

Next == x' = x

====