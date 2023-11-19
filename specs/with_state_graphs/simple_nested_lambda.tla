---- MODULE simple_nested_lambda ----
EXTENDS Naturals

VARIABLE x

\* 
\* Higher order operator definitions.
\* 

M == 83

\* TODO: Eventually need to ideally make this work even when same argument name is used across different ops
\* that call into each other. For now the workaround is to use unique argument names b/w ops that call each other with 
\* parameterized operator args.

\* Op1(g(_)) == g(33)
Op1(f(_)) == f(33)

\* Nested higher order op call chain.
\* Inner LAMBDA def also captures value of top level operator arg.
OpA(g(_), v) == Op1(LAMBDA arg : 2 + g(arg) + v)

\* OpB(f(_), v) == IF v = 1 THEN f(v) + 1 ELSE Op1(LAMBDA arg : 2 + f(arg) + v)

\* OpC(f(_), v) == 
\*     LET InnerOp(a) == a + 12 IN 
\*         Op1(LAMBDA arg : 2 + f(arg) + v)


\* Nested higher order op call chain.
\* Inner LAMBDA def also captures value of top level operator arg.
\* Op6(h(_), v) == Op1(LAMBDA arg : 2 + h(arg) + v)

Init ==
    \/ x = <<"1", OpA(LAMBDA i : i + 13, 64)>>
    \* \/ x = <<"10", Op6(LAMBDA i : i + 13, 65)>>

Next ==
    x' = x

====