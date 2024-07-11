---- MODULE simple_extends_instance_def_parameterized_var_subst_no_clash ----
EXTENDS Sequences, Naturals

D == {"a","b"}
VARIABLES z

M(c) == INSTANCE simple_extends_M8 WITH x <- z[c]

Init == 
    \/ /\ z \in [D -> 0..2]
       /\ M("a")!XCond
    \/ /\ z \in [D -> 0..2]
       /\ M("b")!XCond

Next == z' = z

====