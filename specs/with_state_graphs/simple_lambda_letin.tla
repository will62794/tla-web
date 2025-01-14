---- MODULE simple_lambda_letin ----
EXTENDS Naturals

VARIABLE x

\* 
\* Higher order operator definitions.
\* 

M == 83

Op2(f(_,_), a, b) == f(a, b)
Op4(f(_,_), g(_,_,_),a,b,c) == f(a, b) + g(a,b,c)

Init ==
    \/ x = <<"8", (LET MyOpA(i,j) == i + j IN
                    Op2(MyOpA, 12, 18))>>
    \/ x = <<"9", (LET MyOpA(i,j) == i + j
                    MyOpB(u,v,h) == u + v * h IN
                    Op4(MyOpA, MyOpB, 12, 13, M))>>
    
Next ==
    x' = x

====