---------------------------- MODULE TestLinQueue ----------------------------
\* 
\* Original source: https://github.com/lorin/tla-linearizability/blob/master/TestLinQueue.tla
\* 
EXTENDS LinQueue

Hmk == <<
        \* A enqueues x.
        [op|->"E", val|->"x", proc|->"A"],
        [op|->"Ok", proc|->"A"]
        >>
\* ASSUME L!Complete(Hmk) = Hmk
\* ASSUME L!InvocationsWithoutResponses(Hmk) = {}
\* ASSUME L!Extensions(Hmk) = {{}}
\* ASSUME L!ExtendedHistories(Hmk) = {Hmk}
\* ASSUME IsLinearizableHistory(Hmk)

---------

Enq == [op|->"E", val|->"y", proc|->"B"]
Ok ==  [op|->"Ok", proc|->"B"]
Hmk2 == Hmk \o <<Enq>>
\* ASSUME L!InvocationsWithoutResponses(Hmk2) = {Enq}
\* ASSUME L!Extensions(Hmk2) = {{Ok}}
\* ASSUME L!ExtendedHistories(Hmk2) = {Hmk2 \o <<Ok>>}
\* ASSUME IsLinearizableHistory(Hmk2)
\* ASSUME L!Complete(Hmk2) = Hmk
\* ASSUME L!Complete(Hmk2 \o <<Ok>>) = Hmk2 \o <<Ok>>

Hmk3 == <<
        \* A and B concurrently enqueue x and y.
        [op|->"E", val|->"x", proc|->"A"],
        [op|->"E", val|->"y", proc|->"B"],
        [op|->"Ok", proc|->"B"],
        [op|->"Ok", proc|->"A"],
        \* B dequeues x.
        [op|->"D",  proc|->"B"],
        [op|->"Ok", val|->"x", proc|->"B"],
        \* \* A dequeues y.
        [op|->"D",  proc|->"A"],
        [op|->"Ok", val|->"y", proc|->"A"]
      >>
\* ASSUME L!InvocationsWithoutResponses(Hmk3) = {}
\* ASSUME L!Extensions(Hmk3) = {{}}
\* ASSUME L!ExtendedHistories(Hmk3) = {Hmk3}
\* ASSUME L!Complete(Hmk3) = Hmk3
\* ASSUME IsLinearizableHistory(Hmk3)

---------

H1 == <<
        \* A and B concurrently enqueue x and y.
        [op|->"E", val|->"x", proc|->"A"],
        [op|->"E", val|->"y", proc|->"B"],
        [op|->"Ok", proc|->"B"],
        [op|->"Ok", proc|->"A"],
        \* B dequeues x.
        [op|->"D",  proc|->"B"],
        [op|->"Ok", val|->"x", proc|->"B"],
        \* \* A dequeues y.
        [op|->"D",  proc|->"A"],
        [op|->"Ok", val|->"y", proc|->"A"],
        \* InL!Complete enqueue of z by A.
        [op|->"E", val|->"z", proc|->"A"]>>
\* ASSUME L!InvocationsWithoutResponses(H1) = {[op|->"E", val|->"z", proc|->"A"]}
\* ASSUME L!Extensions(H1) = {{[op|->"Ok", proc|->"A"]}}
\* ASSUME L!ExtendedHistories(H1) = {H1 \o <<[op|->"Ok", proc|->"A"]>>}
\* Strip inL!Complete enqueue of z by A.
\* ASSUME L!Complete(H1) = SubSeq(H1, 1, Len(H1) - 1)
\* ASSUME L!Complete(H1 \o <<[op|->"Ok", proc|->"A"]>>) = H1 \o <<[op|->"Ok", proc|->"A"]>>
\* ASSUME IsLinearizableHistory(H1)

H2 == <<
        [op|->"E", val|->"x", proc|->"A"],
        [op|->"Ok", proc|->"A"],
        [op|->"E", val|->"y", proc|->"B"],
        [op|->"D",  proc|->"A"],
        [op|->"Ok", proc|->"B"],
        [op|->"Ok", val|->"y", proc|->"A"]
>>
\* ASSUME ~IsLinearizableHistory(H2)

H3 == <<
        [op|->"E", val|->"x", proc|->"A"],
        [op|->"D", proc|-> "B"],
        [op|->"Ok", val|->"x", proc|->"B"]>>
\* ASSUME IsLinearizableHistory(H3)

H4 == <<
        [op|->"E", val|->"x", proc|->"A"],
        [op|->"E", val|->"y", proc|->"B"],
        [op|->"Ok", proc|->"A"],
        [op|->"Ok", proc|->"B"],
        [op|->"D", proc|-> "A"],
        [op|->"D", proc|-> "C"],
        [op|->"Ok", val|->"y", proc|->"A"],
        [op|->"Ok", val|->"y", proc|->"C"]
>>
\* ASSUME ~IsLinearizableHistory(H4)

VARIABLE check

Init == 
    \/ check = IsLinearizableHistory(Hmk)
    \/ check = IsLinearizableHistory(Hmk3)
    \* \/ check = IsLinearizableHistory(H2)
    \* \/ check = IsLinearizableHistory(H3)
    \* \/ check = IsLinearizableHistory(H4)

Next == check' = check

=============================================================================
\* Modification History
\* Last modified Sun Oct 21 15:21:29 PDT 2018 by lhochstein
\* Created Sun Oct 21 10:56:40 PDT 2018 by lhochstein