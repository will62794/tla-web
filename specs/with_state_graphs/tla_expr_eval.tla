---- MODULE tla_expr_eval ----
EXTENDS TLC, Naturals, Integers, Sequences

\*
\* Spec used to test that evaluation of TLA expressions is consistent between
\* Javascript based TLA interpreter and TLC. That is, we use TLC as a test
\* oracle, rather than manually writing expected evaluation results for each
\* expression.
\*

VARIABLE exprs

Init == exprs = [
    add |-> 5 + 5,
    mul |-> 3 * 4,
    minus |-> 10 - 3,
    negative1 |-> -3 + 5,
    addparens |-> ((1+2)*4),
    addparens2 |-> (1+2*4),
    not |-> ~TRUE,
    not2 |-> ~FALSE,
    seqlen |-> Len(<<1,2,3>>),
    head1 |-> Head(<<1,2,3>>),
    head2 |-> Head(<<3,2,1>>),
    tail1 |-> Tail(<<1,2,3>>),
    tail2 |-> Tail(<<1>>),
    case1 |-> CASE TRUE -> 3 [] FALSE -> 5,
    case2 |-> CASE FALSE -> 3 [] TRUE -> 5,
    case3 |-> CASE FALSE -> 3 [] FALSE -> 5 [] TRUE -> 7,
    caseother |-> CASE FALSE -> 3 [] FALSE -> 5 [] FALSE -> 7 [] OTHER -> 9,
    implication |-> TRUE => FALSE,
    implication1 |-> FALSE => FALSE,
    implication2 |-> FALSE => TRUE,
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
    except1prev |-> [[a |-> 1, b |-> 2] EXCEPT !["a"] = @ + 44],
    \* except1multi |-> [[a |-> 1, b |-> 2] EXCEPT !["a"] = 10, !["b"] = 11], \* TODO: Handle this case in intepreter.
    exceptnested1 |-> [[a |-> [x |-> 1], b |-> 2] EXCEPT !["a"]["x"] = 12],
    exceptnested2 |-> [[a |-> [x |-> [y |-> 3]], b |-> 2] EXCEPT !["a"]["x"]["y"] = 12],
    fcnapp1 |-> [a |-> 1, b |-> 2]["a"],
    booleanset |-> BOOLEAN
]

\* fcnset1 |-> [{"x","y"} -> {1,2,3}]
    
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