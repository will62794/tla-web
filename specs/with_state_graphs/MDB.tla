---- MODULE MDB ----
EXTENDS Sequences, Naturals

CONSTANTS WC,  \* write concern
          RC   \* read concern

CONSTANTS Keys, 
          Values, 
          NoValue

WCVALUES == {"one", 
             "majority"}

RCVALUES == {"linearizable", 
             "snapshot", 
             "local",
             "available"}

LogIndices == Nat \ {0}

Epochs == Nat \ {0}


\* The result a read will have if no value can be found.
NotFoundReadResult == [
    logIndex |-> 0,
    value |-> NoValue
]

\* Log entries contain one key-value pair each, modeled as a record
LogEntries ==
    [
        key: Keys,
        value: Values
    ]

Logs == Seq(LogEntries)

Max(S) == CHOOSE x \in S : \A y \in S : x >= y


---------------------------------------------------------------------
\* CommitIndex and epoch express a high-level view of
\* underlying processes like replication and failure recovery:
\* - the commitIndex indicates a position in the log (or 0 for no position)
\*   before which data is durable.
\* - the epoch increments strictly monotonically whenever log is non-deterministically
\*   truncated in the range (commitIndex+1)..Len(log)), modeling loss of uncommitted data
\*   due to node failures

VARIABLES log, commitIndex, epoch

mvars == <<log, commitIndex, epoch>>

TypesOK ==
    /\ log \in Logs
    /\ commitIndex \in Nat
    /\ epoch \in Epochs

\* This operator initiates a write, adding it to the log.
WriteInit(key, value) ==
    /\ log' = Append(log, [
            key |-> key,
            value |-> value
       ])

\* For a given key, a read can be entirely defined by a value and a flag:
\* - point is a point in the log to which the read should be applied.
\*   for log entries at or "before" (index <=) point, the latest
\*   value associated with key will be included in the result.
\*   If the log at or before point does not mention the given key at all,
\*   then the result set will include NotFoundReadResult.
\*   An empty set as a result means the read is not possible; any valid read, even
\*   one that returns a "not found" result, will have at least one element in
\*   its set.
\* - allowDirty controls a secondary behavior: for elements of the log
\*   whose index > point, if allowDirty = TRUE then they will also
\*   be included in the result set. If allowDirty = FALSE, then only
\*   the single latest value whose index <= point will be in the result set.
GeneralRead(key, index, allowDirty) ==
    LET maxCandidateIndices == { i \in DOMAIN log :
            /\ log[i].key = key
            /\ i <= index }
        allIndices == { i \in DOMAIN log :
            /\ allowDirty
            /\ log[i].key = key
            /\ i > index }
    IN  { [logIndex |-> i, value |-> log[i].value]
          : i \in allIndices \cup (
            IF   maxCandidateIndices # {}
            THEN {Max(maxCandidateIndices)}
            ELSE {}) } \cup 
        (IF   maxCandidateIndices = {}
         THEN {NotFoundReadResult}
         ELSE {})

Read(key) == CASE
            \* linearizable reads from commitIndex and forbids dirty reads
            RC = "linearizable" -> GeneralRead(key, commitIndex, FALSE)

        \*     \* available reads from readIndex, because the node we reach may be behind commitIndex; 
        \*     \* it also allows dirty reads
        \*  [] RC = "available"    -> GeneralRead(key, readIndex, TRUE)

\* causal hlc read at or more recent than what we received last from a read/write
ReadAtTime(token, key) ==
        IF   TRUE
             \* \/ epoch = token.epoch  \* invalidate token on epoch change
             \* \/ token = [checkpoint |-> 0,epoch |-> 0] \* NoSessionToken hack !!
        THEN LET sessionIndex ==  token.checkpoint \* Max({token.checkpoint, readIndex})
             IN  GeneralRead(key, sessionIndex, TRUE)
        ELSE {}

---------------------------------------------------------------------
\* actions and main spec

\* Expand the prefix of the log that can no longer be lost.
IncreaseCommitIndex ==
    /\ commitIndex' \in commitIndex..Len(log)
    /\ UNCHANGED <<log, epoch>>

\* Any data that is not part of the checkpointed log prefix may be lost at any time. 
TruncateLog ==
    \E i \in (commitIndex+1)..Len(log) :
        /\ log' = SubSeq(log, 1, i - 1)
        /\ epoch' = epoch + 1
        /\ UNCHANGED <<commitIndex>>

\* Init ==
\*     /\ log = <<>>
\*     /\ readIndex = 0
\*     /\ commitIndex = 0
\*     /\ epoch = 1

\* \* This relation models all possible log actions, without performing any write.
\* Next ==
\*     \/ IncreaseCommitIndex
\*     \/ TruncateLog

===============================================================================