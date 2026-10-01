------------------------- MODULE SnapshotIsolation -------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

(**************************************************************************************************)
(*                                                                                                *)
(* This is a specification of snapshot isolation.  It is based on various sources, integrating    *)
(* ideas and definitions from:                                                                    *)
(*                                                                                                *)
(*     ``Making Snapshot Isolation Serializable", Fekete et al., 2005                             *)
(*     https://www.cse.iitb.ac.in/infolab/Data/Courses/CS632/2009/Papers/p492-fekete.pdf          *)
(*                                                                                                *)
(*     ``Serializable Isolation for Snapshot Databases", Cahill, 2009                             *)
(*     https://ses.library.usyd.edu.au/bitstream/2123/5353/1/michael-cahill-2009-thesis.pdf       *)
(*                                                                                                *)
(*     ``A Read-Only Transaction Anomaly Under Snapshot Isolation", Fekete et al.                 *)
(*     https://www.cs.umb.edu/~poneil/ROAnom.pdf                                                  *)
(*                                                                                                *)
(*     ``Debugging Designs", Chris Newcombe, 2011                                                 *)
(*     https://github.com/pron/amazon-snapshot-spec/blob/master/DebuggingDesigns.pdf              *)
(*                                                                                                *)
(* This spec tries to model things at a very high level of abstraction, so as to communicate the  *)
(* important concepts of snapshot isolation, as opposed to how a system might actually implement  *)
(* it.  Correctness properties and their detailed explanations are included at the end of this    *)
(* spec.  We draw the basic definition of snapshot isolation from Definition 1.1 of Fekete's      *)
(* "Read-Only" anomaly paper:                                                                     *)
(*                                                                                                *)
(*                                                                                                *)
(*     "...we assume time is measured by a counter that advances whenever any                     *)
(* transaction starts or commits, and we designate the time when transaction Ti starts as         *)
(* start(Ti) and the time when Ti commits as commit(Ti).                                          *)
(*                                                                                                *)
(* Definition 1.1: Snapshot Isolation (SI).  A transaction Ti executing under SI conceptually     *)
(* reads data from the committed state of the database as of time start(Ti) (the snapshot), and   *)
(* holds the results of its own writes in local memory store, so if it reads data it has written  *)
(* it will read its own output.  Predicates evaluated by Ti are also based on rows and index      *)
(* entry versions from the committed state of the database at time start(Ti), adjusted to take    *)
(* Ti's own writes into account.  Snapshot Isolation also must obey a "First Committer (Updater)  *)
(* Wins" rule...The interval in time from the start to the commit of a transaction, represented   *)
(* [Start(Ti), Commit(Ti)], is called its transactional lifetime.  We say two transactions T1 and *)
(* T2 are concurrent if their transactional lifetimes overlap, i.e., [start(T1), commit(T1)] ∩    *)
(* [start(T2), commit(T2)] ≠ Φ.  Writes by transactions active after Ti starts, i.e., writes by   *)
(* concurrent transactions, are not visible to Ti.  When Ti is ready to commit, it obeys the      *)
(* First Committer Wins rule, as follows: Ti will successfully commit if and only if no           *)
(* concurrent transaction Tk has already committed writes (updates) of rows or index entries that *)
(* Ti intends to write."                                                                          *)
(*                                                                                                *)
(* REPRESENTATION: A TRANSACTION BODY IS ONE EVENT                                                *)
(*                                                                                                *)
(* This module uses the same transaction representation as `TPCC` and `Auction`.  Conflict        *)
(* serializability depends only on each transaction's begin time, commit time, read key set and   *)
(* write key set -- never on the order in which its body operations execute (under SI a           *)
(* transaction's writes are invisible until commit, and its reads see only its begin snapshot, so *)
(* no other transaction observes the body's interleaving).  So a transaction's body is recorded   *)
(* as a single event carrying those two sets, rather than as a sequence of individual read and    *)
(* write events.  This removes any need for reasoning about sequence positions, and makes the     *)
(* analysis a matter of set reasoning.                                                            *)
(*                                                                                                *)
(* Since this module models an *arbitrary* workload (unlike `TPCC` and `Auction`, which fix a set *)
(* of transaction programs), the body of a transaction is chosen nondeterministically when the    *)
(* transaction starts: any read key set and any set of writes assigning one value per written     *)
(* key.                                                                                           *)
(*                                                                                                *)
(**************************************************************************************************)


(**************************************************************************************************)
(* The constant parameters of the spec.                                                           *)
(**************************************************************************************************)

\* Set of all transaction ids.
CONSTANT txnIds

\* Set of all data store keys/values.
CONSTANT keys, values

\* An empty value.
CONSTANT Empty

(**************************************************************************************************)
(* The variables of the spec.                                                                     *)
(**************************************************************************************************)

\* The clock, which measures 'time', is just a counter, that increments (ticks)
\* whenever a transaction starts or commits.
VARIABLE clock

\* The set of all currently running transactions.
VARIABLE runningTxns

\* The full history of all transaction operations. It is modeled as a linear
\* sequence of events: a 'begin' and a 'body' event per started transaction, and a
\* 'commit' or 'abort' event per finished one. Such a history would likely never exist in a
\* real implementation, but it is used in the model to check the properties of snapshot isolation.
VARIABLE txnHistory

\* The key-value data store.
VARIABLE dataStore

\* The set of snapshots needed for all running transactions. Each snapshot
\* represents the entire state of the data store as of a given point in time,
\* adjusted to take the transaction's own writes into account. It is a function from
\* transaction ids to data store snapshots.
VARIABLE txnSnapshots

\* txnId -> the body (reads / writes) that transaction is executing, or Empty if it
\* has not started. Keeping the body here, as well as in the history, lets the commit
\* and abort actions talk about a transaction's writes without searching the history.
VARIABLE txnProg

vars == <<clock, runningTxns, txnSnapshots, dataStore, txnHistory, txnProg>>


(**************************************************************************************************)
(* Data type definitions.                                                                         *)
(*                                                                                                *)
(* A body is a record with two fields: `reads`, the set of keys read, and `writes`, the set of    *)
(* write operations (each a key together with the value written).  The MVSG itself uses only the  *)
(* keys; values are kept so that the modelled data store is meaningful.                           *)
(**************************************************************************************************)

DataStoreType == [keys -> (values \cup {Empty})]

WriteOpType   == [type : {"write"}, key : keys, val : values]
BodyType      == [reads : SUBSET keys, writes : SUBSET WriteOpType]

BeginOpType   == [type : {"begin"}  , txnId : txnIds , time : Nat]
BodyOpType    == [type : {"body"}   , txnId : txnIds , reads : SUBSET keys, writes : SUBSET WriteOpType]
CommitOpType  == [type : {"commit"} , txnId : txnIds , time : Nat, updatedKeys : SUBSET keys]
AbortOpType   == [type : {"abort"}  , txnId : txnIds , time : Nat]
AnyOpType     == UNION {BeginOpType, BodyOpType, CommitOpType, AbortOpType}

WriteKeysOf(B) == {w.key : w \in B.writes}

\* The set of all bodies a transaction may execute: any set of keys read, and any
\* assignment of a value to each key written. Writing a key at most once per transaction
\* loses no generality, since only the last write of a key is ever visible to anyone else.
Bodies ==
    LET WriteSets == UNION {[S -> values] : S \in SUBSET keys} IN
    {[reads  |-> rd,
      writes |-> {[type |-> "write", key |-> k, val |-> wr[k]] : k \in DOMAIN wr}] :
        rd \in SUBSET keys, wr \in WriteSets}

(**************************************************************************************************)
(* The type invariant and initial predicate.                                                      *)
(**************************************************************************************************)

TypeInvariant ==
    \* /\ txnHistory \in Seq(AnyOpType) seems expensive to check with TLC, so disable it.
    /\ dataStore    \in DataStoreType
    /\ txnSnapshots \in [txnIds -> (DataStoreType \cup {Empty})]
    /\ txnProg      \in [txnIds -> (BodyType \cup {Empty})]
    /\ runningTxns  \in SUBSET [ id : txnIds,
                                 startTime  : Nat,
                                 commitTime : Nat \cup {Empty}]

Init ==
    /\ runningTxns = {}
    /\ txnHistory = <<>>
    /\ clock = 0
    /\ txnSnapshots = [id \in txnIds |-> Empty]
    /\ txnProg = [id \in txnIds |-> Empty]
    /\ dataStore = [k \in keys |-> Empty]

(**************************************************************************************************)
(* Helpers for querying transaction histories.                                                    *)
(*                                                                                                *)
(* These are parameterized on a transaction history and a transaction id, if applicable.          *)
(**************************************************************************************************)

\* Generic TLA+ helper.
Range(f) == {f[x] : x \in DOMAIN f}

\* The begin or commit op for a given transaction id.
BeginOp(h, txnId)  == CHOOSE op \in Range(h) : op.txnId = txnId /\ op.type = "begin"
CommitOp(h, txnId) == CHOOSE op \in Range(h) : op.txnId = txnId /\ op.type = "commit"

\* The set of all committed/aborted transaction ids in a given history.
CommittedTxns(h) == {op.txnId : op \in {op \in Range(h) : op.type = "commit"}}
AbortedTxns(h)   == {op.txnId : op \in {op \in Range(h) : op.type = "abort"}}

\* Whether a given transaction read or wrote a given key, read off its body event.
ReadsKey(h, txnId, k)  == \E op \in Range(h) : op.txnId = txnId /\ op.type = "body" /\ k \in op.reads
WritesKey(h, txnId, k) == \E op \in Range(h) : op.txnId = txnId /\ op.type = "body" /\
                              \E w \in op.writes : w.key = k

\* The set of all keys read or written to by a given transaction.
KeysReadByTxn(h, txnId)    == {k \in keys : ReadsKey(h, txnId, k)}
KeysWrittenByTxn(h, txnId) == {k \in keys : WritesKey(h, txnId, k)}

RunningTxnIds == {txn.id : txn \in runningTxns}

(**************************************************************************************************)
(*                                                                                                *)
(* Action Definitions                                                                             *)
(*                                                                                                *)
(**************************************************************************************************)


(**************************************************************************************************)
(* When a transaction starts, it gets a new, unique transaction id and is added to the set of     *)
(* running transactions.  It also "copies" a local snapshot of the data store on which it will    *)
(* perform its reads and writes against.  In a real system, this data would not be literally      *)
(* "copied", but this is the fundamental concept of snapshot isolation i.e.  that each            *)
(* transaction appears to operate on its own local snapshot of the database.                      *)
(*                                                                                                *)
(* The transaction's whole body runs in this same step, and is recorded as a single 'body' event. *)
(* Its reads are served from the snapshot and its writes are applied to the snapshot, not to the  *)
(* data store; the data store is only updated at commit time.                                     *)
(**************************************************************************************************)

\* Fold a body's writes into a snapshot, giving the transaction's final snapshot. Each key is
\* written at most once by a body, so there is no last-writer question.
ApplyWrites(snap, W) ==
    LET WK == {w.key : w \in W}
    IN [k \in DOMAIN snap |-> IF k \in WK THEN (CHOOSE w \in W : w.key = k).val ELSE snap[k]]

StartAndRun(newTxnId, body) ==
    LET newTxn ==
        [ id |-> newTxnId,
            startTime |-> clock+1,
            commitTime |-> Empty] IN
    \* Must choose an unused transaction id. There must be no other operation
    \* in the history that already uses this id.
    /\ ~\E op \in Range(txnHistory) : op.txnId = newTxnId
    \* Exclude uninteresting histories: a transaction must do at least one operation.
    /\ (body.reads \cup WriteKeysOf(body)) /= {}
    \* Save a snapshot of current data store for this transaction, with its own writes
    \* applied, and append its 'begin' and 'body' events to the history.
    /\ txnSnapshots' = [txnSnapshots EXCEPT ![newTxnId] = ApplyWrites(dataStore, body.writes)]
    /\ txnProg' = [txnProg EXCEPT ![newTxnId] = body]
    /\ LET beginOp == [ type  |-> "begin",
                        txnId |-> newTxnId,
                        time  |-> clock+1 ]
           bodyOp  == [ type   |-> "body",
                        txnId  |-> newTxnId,
                        reads  |-> body.reads,
                        writes |-> body.writes ] IN
        txnHistory' = txnHistory \o <<beginOp, bodyOp>>
    \* Add transaction to the set of active transactions.
    /\ runningTxns' = runningTxns \cup {newTxn}
    \* Tick the clock.
    /\ clock' = clock + 1
    /\ UNCHANGED <<dataStore>>


(**************************************************************************************************)
(* When a transaction T0 is ready to commit, it obeys the "First Committer Wins" rule.  T0 will   *)
(* only successfully commit if no concurrent transaction has already committed writes of data     *)
(* objects that T0 intends to write.  Transactions T0, T1 are considered concurrent if the        *)
(* intersection of their timespans is non empty i.e.                                              *)
(*                                                                                                *)
(*     [start(T0), commit(T0)] \cap [start(T1), commit(T1)] != {}                                 *)
(**************************************************************************************************)

\* Checks whether a given transaction is allowed to commit, based on whether it conflicts
\* with other concurrent transactions that have already committed.
TxnCanCommit(txnId) ==
    \E txn \in runningTxns :
        /\ txn.id = txnId
        /\ ~\E op \in Range(txnHistory) :
            /\ op.type = "commit"
            \* Did another transaction commit after I started.
            /\ op.time > txn.startTime
            /\ KeysWrittenByTxn(txnHistory, txnId) \cap op.updatedKeys /= {} \* Must be no conflicting keys.

CommitTxn(txnId) ==
    \* Transaction must be able to commit i.e. have no write conflicts with concurrent.
    \* committed transactions.
    /\ txnId \in RunningTxnIds
    /\ TxnCanCommit(txnId)
    /\ LET commitOp == [ type          |-> "commit",
                         txnId         |-> txnId,
                         time          |-> clock + 1,
                         updatedKeys   |-> KeysWrittenByTxn(txnHistory, txnId)] IN
       txnHistory' = Append(txnHistory, commitOp)
    \* Merge this transaction's updates into the data store. If the
    \* transaction has updated a key, then we use its version as the new
    \* value for that key. Otherwise the key remains unchanged.
    /\ dataStore' = [k \in keys |-> IF k \in KeysWrittenByTxn(txnHistory, txnId)
                                        THEN txnSnapshots[txnId][k]
                                        ELSE dataStore[k]]
    \* Remove the transaction from the active set.
    /\ runningTxns' = {r \in runningTxns : r.id # txnId}
    /\ clock' = clock + 1
    \* We can leave the snapshot and the body around, since they won't be used again.
    /\ UNCHANGED <<txnSnapshots, txnProg>>

(**************************************************************************************************)
(* In this spec, a transaction aborts if and only if it cannot commit, due to write conflicts.    *)
(**************************************************************************************************)
AbortTxn(txnId) ==
    \* If a transaction can't commit due to write conflicts, then it
    \* must abort.
    /\ txnId \in RunningTxnIds
    /\ ~TxnCanCommit(txnId)
    /\ LET abortOp == [ type   |-> "abort",
                        txnId  |-> txnId,
                        time   |-> clock + 1] IN
       txnHistory' = Append(txnHistory, abortOp)
    /\ runningTxns' = {r \in runningTxns : r.id # txnId} \* transaction is no longer running.
    /\ clock' = clock + 1
    \* No changes are made to the data store.
    /\ UNCHANGED <<dataStore, txnSnapshots, txnProg>>

(**************************************************************************************************)
(* The next-state relation and spec definition.                                                   *)
(*                                                                                                *)
(* Since it is desirable to have TLC check for deadlock, which may indicate bugs in the spec or   *)
(* in the algorithm, we want to explicitly define what a "valid" termination state is.  If all    *)
(* transactions have run and either committed or aborted, we consider that valid termination, and *)
(* is allowed as an infinite suttering step.                                                      *)
(**************************************************************************************************)

AllTxnsFinished == AbortedTxns(txnHistory) \cup CommittedTxns(txnHistory) = txnIds

Next ==
    \* Starts a transaction and runs its entire body, which is chosen nondeterministically.
    \/ \E tid \in txnIds, body \in Bodies : StartAndRun(tid, body)
    \* Ends a given transaction by either committing or aborting it.
    \* Assumes that the given transaction is currently running.
    \/ \E tid \in txnIds : CommitTxn(tid)
    \/ \E tid \in txnIds : AbortTxn(tid)
    \/ (AllTxnsFinished /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)


----------------------------------------------------------------------------------------------------


(**************************************************************************************************)
(*                                                                                                *)
(* Correctness Properties and Tests                                                               *)
(*                                                                                                *)
(**************************************************************************************************)



(**************************************************************************************************)
(* An alternative cycle check expressed directly in terms of paths, following the style of the    *)
(* CommunityModules Graphs module (Path / HasCycle):                                              *)
(*                                                                                                *)
(* https://github.com/tlaplus/CommunityModules/blob/master/modules/Graphs.tla                     *)
(*                                                                                                *)
(* This avoids a recursive operator.  A path is a non-empty sequence of nodes in which            *)
(* consecutive nodes are joined by an edge; a cycle is a path that returns to its starting node.  *)
(*                                                                                                *)
(* Graphs.Path uses Seq(G.node) directly, but TLC cannot enumerate Seq of a non-empty set (it is  *)
(* infinite).  Since a cycle, if one exists, can always be taken to be simple, it suffices to     *)
(* consider paths whose length is at most the number of nodes plus one, which is finite and so    *)
(* enumerable by TLC.                                                                             *)
(**************************************************************************************************)

\* The set of all nodes appearing as an endpoint of some edge.
GraphNodes(edges) == {e[1] : e \in edges} \cup {e[2] : e \in edges}

\* The set of all paths of a given graph, i.e. all non-empty sequences of nodes whose consecutive
\* elements are connected by an edge. Path length is bounded by the number of nodes, which keeps
\* the set finite without losing the ability to detect a cycle.
Paths(edges) ==
    LET nodes == GraphNodes(edges)
        maxLen == Cardinality(nodes) + 1
    IN  {p \in UNION {[1..n -> nodes] : n \in 1..maxLen} :
            \A i \in 1..(Len(p)-1) : <<p[i], p[i+1]>> \in edges}

\* A cycle exists iff some path of at least one edge returns to its starting node.
IsCycleViaPath(edges) ==
    \E p \in Paths(edges) : Len(p) > 1 /\ p[1] = p[Len(p)]



(**************************************************************************************************)
(*                                                                                                *)
(* Verifying Serializability                                                                      *)
(*                                                                                                *)
(* ---------------------------------------                                                        *)
(*                                                                                                *)
(* For checking serializability of transaction histories we use the "Conflict Serializability"    *)
(* definition.  This is slightly different than what is known as "View Serializability", but is   *)
(* suitable for verification, since it is efficient to check, whereas checking view               *)
(* serializability of a transaction schedule is known to be NP-complete.                          *)
(*                                                                                                *)
(* The definition of conflict serializability permits a more limited set of transaction           *)
(* histories.  Intuitively, it can be viewed as checking whether a given schedule has the         *)
(* "potential" to produce a certain anomaly, even if the particular data values for a history     *)
(* make it serializable.  Formally, we can think of the set of conflict serializable histories as *)
(* a subset of all possible serializable histories.  Alternatively, we can say that, for a given  *)
(* history H ConflictSerializable(H) => ViewSerializable(H).  The converse, however, is not true. *)
(* A history may be view serializable but not conflict serializable.                              *)
(*                                                                                                *)
(* In order to check for conflict serializability, we construct a multi-version serialization     *)
(* graph (MVSG).  Details on MVSG can be found, among other places, in Cahill's thesis, Section   *)
(* 2.5.1.  To construct the MVSG, we put an edge from one committed transaction T1 to another     *)
(* committed transaction T2 in the following situations:                                          *)
(*                                                                                                *)
(*   (WW-Dependency)                                                                              *)
(*   T1 produces a version of x, and T2 produces a later version of x.                            *)
(*                                                                                                *)
(*   (WR-Dependency)                                                                              *)
(*   T1 produces a version of x, and T2 reads this (or a later) version of x.                     *)
(*                                                                                                *)
(*   (RW-Dependency)                                                                              *)
(*   T1 reads a version of x, and T2 produces a later version of x. This is                       *)
(*   the only case where T1 and T2 can run concurrently.                                          *)
(*                                                                                                *)
(**************************************************************************************************)

\* T1 wrote to a key that T2 then also wrote to. The First Committer Wins rule implies
\* that T1 must have committed before T2 began.
WWDependency(h, t1Id, t2Id) ==
    /\ \E k \in keys : WritesKey(h, t1Id, k) /\ WritesKey(h, t2Id, k)
    /\ CommitOp(h, t1Id).time < CommitOp(h, t2Id).time

\* T1 wrote to a key that T2 then later read, after T1 committed.
WRDependency(h, t1Id, t2Id) ==
    /\ \E k \in keys : WritesKey(h, t1Id, k) /\ ReadsKey(h, t2Id, k)
    /\ CommitOp(h, t1Id).time < BeginOp(h, t2Id).time

\* T1 read a key that T2 then later wrote to. T1 must start before T2 commits, since this implies that T1 read
\* a version of the key and T2 produced a later version of that key, i.e. when it commits. T1, however, read
\* an earlier version of that key, because it started before T2 committed.
RWDependency(h, t1Id, t2Id) ==
    /\ \E k \in keys : ReadsKey(h, t1Id, k) /\ WritesKey(h, t2Id, k)
    /\ BeginOp(h, t1Id).time < CommitOp(h, t2Id).time


\* Produces the serialization graph as defined above, for a given history. This graph is produced
\* by defining the appropriate set comprehension, where the produced set contains all the edges of the graph.
SerializationGraph(history) ==
    LET committedTxnIds == CommittedTxns(history) IN
    {tedge \in (committedTxnIds \X committedTxnIds):
        /\ tedge[1] /= tedge[2]
        /\ \/ WWDependency(history, tedge[1], tedge[2])
           \/ WRDependency(history, tedge[1], tedge[2])
           \/ RWDependency(history, tedge[1], tedge[2])}

\* The key property to verify i.e. serializability of transaction histories, expressed using the
\* path-based cycle check.
IsConflictSerializableViaPath(h) == ~IsCycleViaPath(SerializationGraph(h))

SerializableViaPath == IsConflictSerializableViaPath(txnHistory)


-------------------------------------------------

\* Some model checking details.

Symmetry == Permutations(keys) \cup Permutations(values) \cup Permutations(txnIds)

=============================================================================
\* Modification History
\* Last modified Tue Feb 27 12:56:09 EST 2018 by williamschultz
\* Created Sat Jan 13 08:59:10 EST 2018 by williamschultz
