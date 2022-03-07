---- MODULE tla_expr_eval ----
EXTENDS TLC, Naturals

\*
\* Spec used to test that evaluation of TLA expressions is consistent between
\* Javascript based TLA interpreter and TLC. That is, we use TLC as a test
\* oracle, rather than manually writing expected evaluation results for each
\* expression.
\*

VARIABLE exprs

Init == exprs = [
    add |-> 5 + 5,
    setunion1 |-> {1,2} \cup {2,3},
    setunion2 |-> {1,2,3} \cup {2,3},
    setint1 |-> {1,2,3} \cap {2,3},
    setint2 |-> {1,2,3} \cap {1,2,3},
    setint3 |-> {1,2,3} \cap {},
    setdiff1 |-> {1,2,3} \ {2},
    setmap1 |-> {x : x \in {1,2,3}},
    setmap2 |-> {x + 2 : x \in {1,2,3}},
    setmap3 |-> {x + 2 : x \in {1,2,3} \cup {2,3,4}},
    setfilter1 |-> {x \in {1,2,3} : x > 1},
    except1 |-> [[a |-> 1, b |-> 2] EXCEPT !["a"] = 12],
    fcnapp1 |-> [a |-> 1, b |-> 2]["a"],
    fcnset1 |-> [{"x","y"} -> {1,2,3}]
]
    
Next == UNCHANGED exprs

\* 
\* Some failing cases to look into.
\* 

\* except2 |-> [[a |-> 1, b |-> 2] EXCEPT !["c"] = 3]
\* fcngen1 |-> [i \in {1,2,3} |-> i+2]
\* fcnset2 |-> [{} -> {1,2,3}]
\* fcnset3 |-> [{"x"} -> SUBSET {1,2}]
\* arr |-> {3,2,1}


====