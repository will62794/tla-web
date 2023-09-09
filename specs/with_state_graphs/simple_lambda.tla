---- MODULE simple_lambda ----
EXTENDS Naturals

VARIABLE x

\* 
\* Higher order operator definitions.
\* 

M == 83

Plus(a, b) == a + b

Op1a(f(_)) == f(33)

Op1b(f(_), v) == f(v)

Op2(f(_,_), a, b) == f(a, b)

Op3(a, f(_,_), b) == f(a, b)

Op4(f(_,_), g(_,_,_),a,b,c) == f(a, b) + g(a,b,c)

Init ==
    \/ x = <<"1", Op1a(LAMBDA v: v + 4)>>
    \/ x = <<"2", Op1b(LAMBDA v: v + 4, 12)>>
    \/ x = <<"3", Op2(LAMBDA i,j: i + j, 13, 19)>>
    \/ x = <<"4", Op3(13, LAMBDA i,j: i + j, 13)>>
    \/ x = <<"5", Op4(LAMBDA i,j: i + j, LAMBDA i,j,k: i * j * k, 45, 12, 65)>>
    \/ x = <<"6", Op2(Plus, 59, 12)>>
    \/ x = <<"6", Op2(Plus, 49, M)>>
    \/ x = <<"7", Op4(Plus, LAMBDA i,j,k: i * j * k, 45, 12, 65)>>
    \* LET defined operator used an argument to higher order operator.
    \/ x = <<"8", (LET MyOpA(i,j) == i + j IN
                    Op2(MyOpA, 12, 18))>>
    \/ x = <<"9", (LET MyOpA(i,j) == i + j
                    MyOpB(u,v,h) == u + v * h IN
                    Op4(MyOpA, MyOpB, 12, 13, M))>>
    
Next ==
    x' = x

====