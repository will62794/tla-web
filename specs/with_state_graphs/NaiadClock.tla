----------------------------- MODULE NaiadClock -----------------------------
EXTENDS Naturals, Integers, FiniteSets, Sequences

CONSTANT Point   \* Set of points {p1, p2, p3}
CONSTANT Proc    \* Set of processors {a, b}

NatB == 0..30
PointToNat == [Point -> 0..3]

PointRelationType == [Point -> [Point -> BOOLEAN]]

(* Definition of a partial order. *)
IsPartialOrder(leq) ==
    /\ \A s, t, u \in Point : leq[s][t] /\ leq[t][u] => leq[s][u] \* transitive
    /\ \A s, t \in Point : leq[s][t] /\ leq[t][s] => s = t \* antisymmetric
    /\ \A s \in Point : leq[s][s] \* reflexive

(* Exact sequences *)
ExactSeqEach(Q, S) ==
    \A s \in S : \E i \in 1..Len(Q) : Q[i] = s

ExactSeqOnce(Q) ==
    \A i, j \in 1..Len(Q) : Q[i] = Q[j] => i = j

IsExactSeqFor(Q, S) ==
    /\ Q \in Seq(S)
    /\ ExactSeqEach(Q, S)
    /\ ExactSeqOnce(Q)

ExactSeqFor(S) == CHOOSE Q \in Seq(S) : IsExactSeqFor(Q, S)

(* Delta vectors *)
DeltaVecType == [Point -> Int]
DeltaVecZero == [t \in Point |-> 0]
DeltaVecAdd(a, b) == [t \in Point |-> a[t] + b[t]]
DeltaVecNeg(a) == [t \in Point |-> 0 - a[t]]

(* A delta vector v is vacant up to point t *)
IsDeltaVecVacantUpto(leq, v, t) ==
        \A s \in Point : leq[s][t]  => v[s] = 0

(* A delta vector v is non-positive up to point t *)
IsDeltaVecNonposUpto(leq, v, t) ==
        \A s \in Point : leq[s][t] => ~(v[s] > 0)

(* A delta vector v is supported at point t *)
IsDeltaVecSupported(leq, v, t) ==
        \E s \in Point :
            /\ leq[s][t] /\ s /= t
            /\ v[s] < 0
            /\ IsDeltaVecNonposUpto(leq, v, s)

(* A delta vector v is upright *)
IsDeltaVecUpright(leq, v) ==
        \A t \in Point : v[t] > 0 => IsDeltaVecSupported(leq, v, t)

(* Summing up a sequence of delta vectors, skipping the first k *)
DeltaVecSeqSkipSum(k, Q) ==
    LET
        Zero == DeltaVecZero
        Add(a, b) == DeltaVecAdd(a, b)
        n == Len(Q)
        Elem(i) == IF k < i /\ i <= n THEN Q[i] ELSE Zero
        Sumv[i \in NatB] ==
            IF i = 0 THEN Zero ELSE Add(Sumv[i - 1], Elem(i))
    IN
        Sumv[n]

(* The sum of a sequence of delta vectors *)
DeltaVecSeqSum(Q) == DeltaVecSeqSkipSum(0, Q)

(* Construct a sequence of delta vectors like Q but add d to element Q[n] *)
DeltaVecSeqAddAt(Q, n, d) ==
    LET
        \* Zero == DeltaVecZero
        Add(a, b) == DeltaVecAdd(a, b)
    IN
        [Q EXCEPT ![n] = Add(Q[n], d)]

(* Summing delta vectors in the range of a function *)
DeltaVecFunIndexSum(F, I) ==
    LET
        \* Zero == DeltaVecZero
        \* Add(a, b) == DeltaVecAdd(a, b)
        SeqSum(Q) == DeltaVecSeqSum(Q)
    IN
        SeqSum([i \in 1..Len(I) |-> F[I[i]]])

DeltaVecFunSubsetSum(F, S) ==
        DeltaVecFunIndexSum(F, ExactSeqFor(S))

DeltaVecFunHasFiniteNonZeroRange(F) ==
        IsFiniteSet({d \in DOMAIN F : F[d] /= DeltaVecZero})

DeltaVecFunSum(F) ==
        DeltaVecFunSubsetSum(F, {d \in DOMAIN F : F[d] /= DeltaVecZero})

(* Modify a function by adding v to component x *)
DeltaVecFunAddAt(F, x, v) ==
    LET
        Add(a, b) == DeltaVecAdd(a, b)
    IN
        [F EXCEPT ![x] = Add(F[x], v)]

(* Other data types *)

(* A count vector gives a count of records for each point *)
CountVecType == [Point -> NatB]

(* State variables *)
VARIABLE lleq   \* Precedence between points
VARIABLE nrec   \* Record count at each point
VARIABLE glob   \* Global count for each processor and point
VARIABLE temp   \* Temporary count for each processor and point
VARIABLE msg    \* Clock message queues between processors

(* Fiducial variables *)
VARIABLE nrecvut   \* Previous state: nrec was vacant up to point t
VARIABLE globvut   \* Previous state: glob was vacant up to point t

vars == <<lleq, nrec, glob, temp, msg, nrecvut, globvut>>

(* State operators *)

(* All points s up to t have no records *)
NrecVacantUpto(t) == IsDeltaVecVacantUpto(lleq, nrec, t)

(* All points s up to t have zero in glob[q] *)
GlobVacantUpto(q, t) == IsDeltaVecVacantUpto(lleq, glob[q], t)

(* Sum of delta vectors on the message queue from p to q, skipping the first k, plus temp[p] *)
IncomingInfo(k, p, q) ==
    LET
        sum == DeltaVecSeqSkipSum(k, msg[p][q])
    IN
        DeltaVecAdd(sum, temp[p])

(* Sum of all incoming information for processor q, excluding first k updates from processor p *)
GlobalIncomingInfo(k, p, q) ==
    LET
        F == [xp \in Proc |-> 
               LET xk == IF xp = p THEN k ELSE 0
               IN IncomingInfo(xk, xp, q)]
    IN
        DeltaVecFunSum(F)

(* Next state relations *)

(* Common updates for each next action *)
NextCommon ==
    /\ UNCHANGED lleq
    \* Fiducial variables computed based on old state
    /\ nrecvut' = [ft \in Point |-> NrecVacantUpto(ft)]
    /\ globvut' = [fq \in Proc |-> [ft \in Point |-> GlobVacantUpto(fq, ft)]]

(* Perform an operation *)
NextPerformOperation ( p, c, r) ==
        LET
            delta == [t \in Point |-> r[t] - c[t]]
        IN
            /\ \A t \in Point : c[t] <= nrec[t]  \* Consume only existing records
            /\ IsDeltaVecUpright(lleq, delta)   \* Delta must be upright
            /\ nrec' = DeltaVecAdd(nrec, delta)
            /\ temp' = [temp EXCEPT ![p] = DeltaVecAdd(temp[p], delta)]
            /\ UNCHANGED glob
            /\ UNCHANGED msg
            /\ NextCommon

(* Send an update *)
NextSendUpdate (p, tt) ==
        LET
            tempp == temp[p]
            gamma == [t \in Point |-> IF t \in tt THEN tempp[t] ELSE 0]
            newtempp == [t \in Point |-> IF t \in tt THEN 0 ELSE tempp[t]]
        IN
            /\ gamma /= DeltaVecZero
            /\ IsDeltaVecUpright(lleq, newtempp)
            /\ temp' = [temp EXCEPT ![p] = newtempp]
            /\ msg' = [msg EXCEPT ![p] = [q \in Proc |-> Append(msg[p][q], gamma)]]
            /\ UNCHANGED nrec
            /\ UNCHANGED glob
            /\ NextCommon

(* Receive an update *)
NextReceiveUpdate (p, q) ==
            /\ msg[p][q] /= << >>
            /\ glob' = [glob EXCEPT ![q] = DeltaVecAdd(glob[q], Head(msg[p][q]))]
            /\ msg' = [msg EXCEPT ![p][q] = Tail(msg[p][q])]
            /\ UNCHANGED nrec
            /\ UNCHANGED temp
            /\ NextCommon

(* Initialization *)
Init ==
    /\ lleq \in PointRelationType
    /\ IsPartialOrder(lleq)               \* Any partial order
    /\ nrec \in PointToNat                \* Any initial record-point arrangement
    /\ glob = [p \in Proc |-> nrec]       \* Initial values
    /\ temp = [p \in Proc |-> DeltaVecZero]
    /\ msg = [p \in Proc |-> [q \in Proc |-> << >>]]
    /\ nrecvut = [ft \in Point |-> NrecVacantUpto(ft)]
    /\ globvut = [fp \in Proc |-> [ft \in Point |-> GlobVacantUpto(fp, ft)]]

(* Next state relation *)
Next ==
    \/ \E p \in Proc, c,r \in PointToNat  : NextPerformOperation (p,c,r)
    \/ \E p \in Proc, tt \in SUBSET Point : NextSendUpdate (p, tt)
    \/ \E p, q \in Proc : NextReceiveUpdate (p, q)

(* Specification *)
Spec ==
    Init /\ [][Next]_vars

(* Invariants *)

(* Only a finite number of processors have information in temp *)
IsFiniteTempProcs ==
    IsFiniteSet({p \in Proc : temp[p] /= DeltaVecZero})

(* Only a finite number of processors are sending messages to any q *)
IsFiniteMsgSenders ==
    \A q \in Proc :
        IsFiniteSet({p \in Proc : msg[p][q] /= << >>})

(* State variables have the correct types *)
InvType ==
    /\ lleq \in PointRelationType
    /\ nrec \in CountVecType
    /\ glob \in [Proc -> DeltaVecType]
    /\ temp \in [Proc -> DeltaVecType]
    /\ msg \in [Proc -> [Proc -> Seq(DeltaVecType)]]
    /\ nrecvut \in [Point -> BOOLEAN]
    /\ globvut \in [Proc -> [Point -> BOOLEAN]]
    /\ IsPartialOrder(lleq)
    /\ IsFiniteTempProcs
    /\ IsFiniteMsgSenders

(* For all processors p, temp[p] is an upright delta vector *)
InvTempUpright ==
    \A p \in Proc : IsDeltaVecUpright(lleq, temp[p])

(* Sum of all incoming info heading toward q (after skipping the first k
   updates on the message queue) is upright *)
InvIncomingInfoUpright ==
    \A k \in NatB :
    \A p, q \in Proc :
        IsDeltaVecUpright(lleq, IncomingInfo(k, p, q))

(* Sum of all incoming info heading toward q, plus glob[q], equals nrec *)
InvGlobalRecordCount ==
    \A q \in Proc :
        nrec = DeltaVecAdd(GlobalIncomingInfo(0, q, q), glob[q])

(* If GlobVacantUpto(q, t) holds, then all points s up to t have no records *)
InvGlobVacantUptoImpliesNrec ==
    \A q \in Proc :
    \A t \in Point :
        GlobVacantUpto(q, t) => NrecVacantUpto(t)

(* Safety properties *)

(* For all points t, if NrecVacantUpto(t) holds, it remains true *)
SafeStickyNrecVacantUpto ==
    \A t \in Point : NrecVacantUpto(t) => []NrecVacantUpto(t)

(* For all processors q and points t, if GlobVacantUpto(q, t) holds, it remains true *)
SafeStickyGlobVacantUpto ==
    \A q \in Proc :
    \A t \in Point :
        GlobVacantUpto(q, t) => []GlobVacantUpto(q, t)

(* Invariant: For all points t, nrecvut[t] is sticky *)
InvStickyNrecVacantUpto ==
    \A t \in Point :
        nrecvut[t] => NrecVacantUpto(t)

(* Invariant: For all processors q and points t, globvut[q][t] is sticky *)
InvStickyGlobVacantUpto ==
    \A q \in Proc :
    \A t \in Point :
        globvut[q][t] => GlobVacantUpto(q, t)

(* Safety property: For all q and t, if GlobVacantUpto(q, t), then for all following states,
   all points s up to t have no records *)
SafeGlobVacantUptoImpliesStickyNrec ==
    \A q \in Proc :
    \A t \in Point :
        GlobVacantUpto(q, t) => []NrecVacantUpto(t)



=============================================================================
\* make point to be point point type, proc to be proctype  
\* guard next statements to be able to use tla-web

(* A delta vector v is vacant up to point t *)
IsDeltaVecVacantUpto(leq, v, t) ==
    LET
        a \preceq b == leq[a][b]
        a \prec b == leq[a][b] /\ a /= b
    IN
        \A s \in Point : s \preceq t => v[s] = 0

(* A delta vector v is non-positive up to point t *)
IsDeltaVecNonposUpto(leq, v, t) ==
    LET
        a \preceq b == leq[a][b]
        a \prec b == leq[a][b] /\ a /= b
    IN
        \A s \in Point : s \preceq t => ~(v[s] > 0)

(* A delta vector v is supported at point t *)
IsDeltaVecSupported(leq, v, t) ==
    LET
        a \preceq b == leq[a][b]
        a \prec b == leq[a][b] /\ a /= b
    IN
        \E s \in Point :
            /\ s \prec t
            /\ v[s] < 0
            /\ IsDeltaVecNonposUpto(leq, v, s)

(* A delta vector v is upright *)
IsDeltaVecUpright(leq, v) ==
    LET
        a \preceq b == leq[a][b]
        a \prec b == leq[a][b] /\ a /= b
    IN
        \A t \in Point : v[t] > 0 => IsDeltaVecSupported(leq, v, t)


(* Final specification with invariants *)
SpecWithInvariants ==
    Spec /\ InvType /\ InvTempUpright /\ InvIncomingInfoUpright /\
    InvGlobalRecordCount /\ InvGlobVacantUptoImpliesNrec /\
    InvStickyNrecVacantUpto /\ InvStickyGlobVacantUpto

================