---- MODULE simple_lambda ----
EXTENDS Naturals

VARIABLE x

\* 
\* Higher order operator definitions.
\* 

Op1a(f(_)) == f(33)

Op1b(f(_), v) == f(v)

Op2(f(_,_), a, b) == f(a, b)

Op3(a, f(_,_), b) == f(a, b)

Op4(f(_,_), g(_,_,_),a,b,c) == f(a, b) + g(a,b,c)

Init ==
    \/ x = <<"op1a", Op1a(LAMBDA v: v + 4)>>
    \/ x = <<"op1b", Op1b(LAMBDA v: v + 4, 12)>>
    \/ x = <<"op2", Op2(LAMBDA i,j: i + j, 13, 19)>>
    \/ x = <<"op3", Op3(13, LAMBDA i,j: i + j, 13)>>
    \/ x = <<"op4", Op4(LAMBDA i,j: i + j, LAMBDA i,j,k: i * j * k, 45, 12, 65)>>
    
Next ==
    x' = x

====