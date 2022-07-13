---- MODULE tla_expr_eval ----
EXTENDS TLC, Naturals, Integers, Sequences, FiniteSets

\*
\* Spec used to test that evaluation of TLA expressions is consistent between
\* Javascript based TLA interpreter and TLC. That is, we use TLC as a test
\* oracle, rather than manually writing expected evaluation results for each
\* expression.
\*

VARIABLE exprs

Init == exprs = [

    \* Infix numeric ops.
    lt1 |-> 5 < 6,
    lt2 |-> 6 < 5,
    gt1 |-> 6 > 5,
    gt2 |-> 5 > 6,
    geq1 |-> 5 <= 6,
    geq2 |-> 6 <= 5,
    leq1 |-> 5 >= 6,
    leq2 |-> 6 >= 5,
    add |-> 5 + 5,
    mul |-> 3 * 4,
    minus |-> 10 - 3,
    negative1 |-> -3 + 5,
    addparens |-> ((1+2)*4),
    addparens2 |-> (1+2*4),

    \* Boolean ops.
    not |-> ~TRUE,
    not2 |-> ~FALSE,
    implication |-> TRUE => FALSE,
    implication1 |-> FALSE => FALSE,
    implication2 |-> FALSE => TRUE,
    booleanset |-> BOOLEAN,

    \* Sequence operators.
    seqlen |-> Len(<<1,2,3>>),
    head1 |-> Head(<<1,2,3>>),
    head2 |-> Head(<<3,2,1>>),
    tail1 |-> Tail(<<1,2,3>>),
    tail2 |-> Tail(<<1>>),
    domain1 |-> DOMAIN [a |-> 1, b |-> 2, c |-> 3],
    domain2 |-> DOMAIN <<1,2,3>>,
    domain3 |-> DOMAIN <<>>,

    \* CASE construct.
    case1 |-> CASE TRUE -> 3 [] FALSE -> 5,
    case2 |-> CASE FALSE -> 3 [] TRUE -> 5,
    case3 |-> CASE FALSE -> 3 [] FALSE -> 5 [] TRUE -> 7,
    caseother |-> CASE FALSE -> 3 [] FALSE -> 5 [] FALSE -> 7 [] OTHER -> 9,
    
    \* Set operators.
    set1 |-> {1,2,3,3},
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
    subset1 |-> SUBSET {1,2,3},
    card1 |-> Cardinality({1,2,3}),
    card2 |-> Cardinality({1,2,3,3}),

    \* Records/functions.
    except1 |-> [[a |-> 1, b |-> 2] EXCEPT !["a"] = 12],
    except1prev |-> [[a |-> 1, b |-> 2] EXCEPT !["a"] = @ + 44],
    \* except1multi |-> [[a |-> 1, b |-> 2] EXCEPT !["a"] = 10, !["b"] = 11], \* TODO: Handle this case in intepreter.
    exceptnested1 |-> [[a |-> [x |-> 1], b |-> 2] EXCEPT !["a"]["x"] = 12],
    exceptnested2 |-> [[a |-> [x |-> [y |-> 3]], b |-> 2] EXCEPT !["a"]["x"]["y"] = 12],
    fcnapp1 |-> [a |-> 1, b |-> 2]["a"],
    fcnset1 |-> [{1,2} -> {4,5}],
    fcnset2 |-> [{"a","b","c"} -> {4,5}],
    fcnset3 |-> [{"a","b","c"} -> {{1,2},{3,4}}],
    fcnset4 |-> [{"x"} -> SUBSET {1,2}],
    fcnbuild1 |-> [i \in {0,1} |-> 0],
    fcnexpr1 |-> (0 :> 1),
    fcnexpr2 |-> (0 :> 1 @@ 2 :> 3),
    fcnexpr3 |-> (0 :> 1 @@ 2 :> 3 @@ 2 :> 4),

    \* Quantifiers.
    exists1 |-> \E x \in {1,2,3} : x > 2,
    exists2 |-> \E x \in {1,2,3} : x = 4,
    forall1 |-> \A x \in {1,2,3} : x > 2,
    forall2 |-> \A x \in {1,2,3} : x < 5,
    
    bottom |-> TRUE
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