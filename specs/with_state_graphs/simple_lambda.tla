---- MODULE simple_lambda ----
EXTENDS Naturals, Sequences

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

Max(S) == CHOOSE xv \in S : \A y \in S : xv >= y

SelectLastInSeq(seq, TestFcn(_)) ==
  LET I == { i \in 1..Len(seq) : TestFcn(seq[i]) }
  IN IF I # {} THEN Max(I) ELSE 0

RwTxRequest == "RwTxRequest"
RoTxRequest == "RoTxRequest"

history == <<[type |-> RwTxRequest, value |-> 1], [type |-> RoTxRequest, value |-> 2]>>
history2 == <<[type |-> RwTxRequest, value |-> 4], [type |-> RoTxRequest, value |-> 5], [type |-> RoTxRequest, value |-> 5]>>

TestVal ==
    SelectLastInSeq(history, LAMBDA e : e.type \in {RwTxRequest})

TestVal2 ==
    SelectLastInSeq(history2, LAMBDA e : e.type \in {"RwTxRequest", "RoTxRequest"})


Init ==
    \/ x = <<"1", Op1a(LAMBDA v: v + 4)>>
    \/ x = <<"2", Op1b(LAMBDA v: v + 4, 12)>>
    \/ x = <<"3", Op2(LAMBDA i,j: i + j, 13, 19)>>
    \/ x = <<"4", Op3(13, LAMBDA i,j: i + j, 13)>>
    \/ x = <<"5", Op4(LAMBDA i,j: i + j, LAMBDA i,j,k: i * j * k, 45, 12, 65)>>
    \/ x = <<"6", Op2(Plus, 59, 12)>>
    \/ x = <<"6", Op2(Plus, 49, M)>>
    \/ x = <<"7", Op4(Plus, LAMBDA i,j,k: i * j * k, 45, 12, 65)>>
    \/ x = TestVal
    \/ x = TestVal2

Next ==
    x' = x

====