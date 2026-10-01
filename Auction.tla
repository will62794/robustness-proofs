------------------------------------ MODULE Auction ------------------------------------
(**************************************************************************************************)
(*                                                                                                *)
(* A TLA+ model of the auction application from Bernardi & Gotsman, "Robustness against           *)
(* Consistency Models with Atomic Visibility" (CONCUR 2016), running on top of a key-value store  *)
(* that provides SNAPSHOT ISOLATION.                                                              *)
(*                                                                                                *)
(* The snapshot isolation layer is modelled directly here -- begin snapshot, read-your-own-       *)
(* writes, the First-Committer-Wins write-conflict rule, and the multi-version serialization      *)
(* graph (MVSG) used to decide conflict serializability -- in exactly the form `TPCC` uses.       *)
(* This module adds a *workload*: it constrains which keys each transaction reads and writes, so  *)
(* that the transactions are the four programs of the paper's running example rather than         *)
(* arbitrary ones.                                                                                *)
(*                                                                                                *)
(* THE QUESTION                                                                                   *)
(*                                                                                                *)
(*     Is every history produced by running the auction programs under snapshot isolation         *)
(*     conflict serializable?  (invariant `SerializableViaPath`)                                  *)
(*                                                                                                *)
(* The answer depends on the transaction mix, and the paper's own two headline analyses are the   *)
(* two sides of it:                                                                               *)
(*                                                                                                *)
(*   * StoreBid + ViewItem -- ROBUST.  §2 and §6 prove that every PSI (hence every SI) execution  *)
(*     of these two programs has a serializable history.  The reason is structural: no cycle in   *)
(*     the MVSG carries two consecutive rw-anti-dependency edges.  (Individual rw edges abound -- *)
(*     every ViewItem -> StoreBid edge, and also StoreBid -> StoreBid between two serialized      *)
(*     StoreBids -- but they never line up twice around a cycle.)  Config `auction-robust`.       *)
(*                                                                                                *)
(*   * RegUser -- NOT ROBUST.  Two concurrent RegUsers registering the same nickname miss each    *)
(*     other's uniqueness check and both insert, producing the write skew of Figure 2(d).  That   *)
(*     is an SI-critical cycle, hence a genuinely non-serializable history.  Config               *)
(*     `auction-reguser`.                                                                         *)
(*                                                                                                *)
(* REPRESENTATION: A TRANSACTION BODY IS ONE EVENT                                                *)
(*                                                                                                *)
(* Conflict serializability depends only on each transaction's begin time, commit time, read key  *)
(* set and write key set -- never on the order in which its body operations execute (under SI a   *)
(* transaction's writes are invisible until commit, and its reads see only its begin snapshot, so *)
(* no other transaction observes the body's interleaving).  So the body is recorded as a single   *)
(* event carrying those two sets, rather than as a sequence of individual read/write events.      *)
(* This removes the need for a recursive sequence-concatenation operator (`Flatten`), which       *)
(* TLAPS cannot unfold, and makes the workload analysis a matter of set reasoning.                *)
(*                                                                                                *)
(* The only thing carried beyond the key sets is the value of each write, because two stored      *)
(* values steer control flow: USERS.name decides whether a RegUser may run at all, and            *)
(* ITEMS.nbids is the read-modify-written counter of StoreBid.                                    *)
(*                                                                                                *)
(* GRANULARITY (why this module has no `ColumnGranularity` knob)                                  *)
(*                                                                                                *)
(* TPCC carries a `ColumnGranularity` constant because at row granularity two TPC-C transactions  *)
(* that share a row but touch disjoint columns manufacture a false dependency edge.  No such pair *)
(* exists in the auction schema: the only row with several fields is ITEMS(desc, nbids), and      *)
(* while ViewItem reads `desc`, no program ever writes it; every other table is effectively       *)
(* single-column.  Row and column granularity therefore induce the same dependency graph here, so *)
(* the knob would be decorative and is omitted.  Predicate reads are still modelled as range      *)
(* scans (below), which is the one granularity choice that does matter.                           *)
(*                                                                                                *)
(**************************************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences, Functions

(**************************************************************************************************)
(* Scale factors.  Keep them tiny: the interesting structure of the auction shows up at two       *)
(* items, two users and two or three transactions.                                                *)
(**************************************************************************************************)

CONSTANT NumItems      \* rows in ITEMS
CONSTANT NumUsers      \* rows USERS can ever hold (the uId domain)
CONSTANT NumNames      \* distinct nicknames a RegUser may request
CONSTANT NumTxns       \* how many transactions may run in a behaviour

\* Which of the four auction programs are allowed to run.  Subset of
\* {"RegUser", "ViewUsers", "StoreBid", "ViewItem"}.
CONSTANT EnabledTxnTypes

\* The "does not exist" / NULL value.
CONSTANT Empty

IIds   == 1..NumItems
UIds   == 1..NumUsers
NIds   == 1..NumNames
TxnIds == 1..NumTxns

\* Largest value ITEMS.nbids can ever take: items start at 0 and only StoreBid increments, once
\* per committed StoreBid, and there are at most NumTxns transactions.
MaxNbids == NumTxns

Tag == "v"

AllTxnTypes == {"RegUser", "ViewUsers", "StoreBid", "ViewItem"}

ASSUME EnabledTxnTypes \subseteq AllTxnTypes
ASSUME NumTxnsNat == NumTxns \in Nat

----------------------------------------------------------------------------------------------------

(**************************************************************************************************)
(*                                                                                                *)
(* The schema (Figure 1).                                                                         *)
(*                                                                                                *)
(*     USERS(uId, name)                                                                           *)
(*     ITEMS(iId, desc, nbids)                                                                    *)
(*     BIDS(bId, iId, val)                                                                        *)
(*                                                                                                *)
(* Conflict serializability is a property of the *access pattern*, not of the data, so we keep    *)
(* only the state that steers control flow or is checked by an invariant:                         *)
(*                                                                                                *)
(*   * USERS(uId).name -- read by RegUser's uniqueness check and by ViewUsers; its value is the   *)
(*     only thing that decides whether RegUser inserts.  Stored exactly.                          *)
(*   * ITEMS(iId).nbids -- read-modify-written by StoreBid and read by ViewItem.  Stored exactly, *)
(*     because it is what makes the lost-update / write-conflict behaviour observable.            *)
(*   * ITEMS(iId).desc -- never read or written by any program; dropped.                          *)
(*   * BIDS(bId, iId, val) -- StoreBid's insert-only output.  No program reads BIDS, and each     *)
(*     StoreBid uses a fresh bId, so it can never conflict.  Modelled with one fresh key per      *)
(*     transaction (the same aggregation TPCC makes for HISTORY).                                 *)
(*                                                                                                *)
(**************************************************************************************************)

ItemKey(i) == [tbl |-> "ITEM", i |-> i]
UserKey(u) == [tbl |-> "USER", u |-> u]
BidKey(t)  == [tbl |-> "BID",  t |-> t]

RowKeys == {ItemKey(i) : i \in IIds} \cup
           {UserKey(u) : u \in UIds} \cup
           {BidKey(t)  : t \in TxnIds}

Keys == RowKeys

\* Presence: a key holds `Empty` iff it has no row.  For USERS the stored value is the nickname;
\* for ITEMS it is the bid count; a BIDS row is just a marker.
RowExists(snap, k) == snap[k] # Empty

----------------------------------------------------------------------------------------------------

(**************************************************************************************************)
(* Variables.                                                                                     *)
(**************************************************************************************************)

VARIABLE clock          \* ticks on every begin and commit
VARIABLE runningTxns    \* set of in-flight transactions
VARIABLE txnHistory     \* the linear event history, the thing we check serializability of
VARIABLE dataStore      \* the committed key-value store
VARIABLE txnSnapshots   \* per-transaction snapshot of the store
VARIABLE txnReq         \* txnId -> the auction request this transaction is executing
VARIABLE txnProg        \* txnId -> the body this request expands to (reads / writes)

vars == <<clock, runningTxns, txnSnapshots, dataStore, txnHistory, txnReq, txnProg>>

(**************************************************************************************************)
(*                                                                                                *)
(* The operations a transaction body consists of.                                                 *)
(*                                                                                                *)
(* A body is a record with two fields: `reads`, the set of keys read, and `writes`, the set of    *)
(* write operations (each a key together with the value written).  The MVSG itself uses only the  *)
(* keys; the values are kept because they steer control flow.                                     *)
(*                                                                                                *)
(**************************************************************************************************)

\* The values a write may carry: a nickname (RegUser), a bid count (StoreBid's update of
\* ITEMS.nbids), or the opaque row marker (StoreBid's BIDS insert).  Stated as a predicate rather
\* than a set, because TLC will not build a set that mixes strings with integers.
\* The value a write may carry is determined by the table it writes: a bid count for ITEMS, a
\* nickname for USERS, the opaque row marker for BIDS.  Typing it per table (rather than by one
\* union `{Tag, Empty} \cup Nat`) keeps every comparison within a single type, which is what TLC
\* requires.
ValsOf(tbl) ==
    CASE tbl = "ITEM" -> 0..MaxNbids
      [] tbl = "USER" -> NIds
      [] tbl = "BID"  -> {Tag}

IsWriteOp(w) ==
    /\ DOMAIN w = {"type", "key", "val"}
    /\ w.type = "write" /\ w.key \in Keys /\ w.val \in ValsOf(w.key.tbl)

IsBody(B) ==
    /\ DOMAIN B = {"reads", "writes"}
    /\ B.reads \subseteq Keys
    /\ \A w \in B.writes : IsWriteOp(w)

WriteKeysOf(B) == {w.key : w \in B.writes}

(**************************************************************************************************)
(* Generic helpers.                                                                               *)
(**************************************************************************************************)

CommittedTxns(h) == {op.txnId : op \in {op \in Range(h) : op.type = "commit"}}
AbortedTxns(h)   == {op.txnId : op \in {op \in Range(h) : op.type = "abort"}}

----------------------------------------------------------------------------------------------------

(**************************************************************************************************)
(*                                                                                                *)
(* The auction programs (Figure 1).                                                               *)
(*                                                                                                *)
(* ----------------------------------------------------------------------------------------      *)
(* PREDICATE READS AND PHANTOMS                                                                   *)
(*                                                                                                *)
(* RegUser does not address a row by primary key; it evaluates a predicate over USERS.name.  If   *)
(* it only recorded reads of the rows that *matched*, a concurrent RegUser that inserts a row     *)
(* with the same nickname would leave no trace, and the write-skew anti-dependency would be       *)
(* missed.  So the predicate is modelled as a *range scan*: RegUser reads every uId in the        *)
(* domain, present or absent.  This is both sound and what an engine without predicate locking    *)
(* does, and it is exactly the edge that makes the RegUser transaction non-robust.                *)
(*                                                                                                *)
(**************************************************************************************************)

(*----------------------------------------------------------------------------------------------*)
(* RegUser(uname).                                                                               *)
(*                                                                                               *)
(* SELECT name FROM USERS WHERE name = uname; if a row matches, abort; else INSERT a new row      *)
(* with a fresh uId and this nickname.                                                            *)
(*                                                                                               *)
(* The conditional abort is modelled by *not running* an instance whose uniqueness check would    *)
(* fail against its begin snapshot (see `ReqEnabled`).  Aborted transactions are elided from the  *)
(* histories the paper reasons about, so omitting them does not change the set of committed       *)
(* histories or the MVSG built over them -- while still requiring the scan reads, which do leave  *)
(* the anti-dependency edges.  The uId is a client-supplied fresh id; inserting a taken uId would *)
(* be a write-write conflict, handled by First-Committer-Wins.                                    *)
(*                                                                                               *)
(* NOTE: the paper's RegUser is the source of the write skew.  Two concurrent instances with the  *)
(* same uname both scan, both see no match, and both insert rows with different uIds -- a cycle   *)
(* of the form RegUser --rw--> RegUser --rw--> RegUser that no serial order can produce.          *)
(*----------------------------------------------------------------------------------------------*)
RegUserProgram(req, snap) ==
    [ reads  |-> {UserKey(x) : x \in UIds},
      writes |-> {[type |-> "write", key |-> UserKey(req.uid), val |-> req.name]} ]

(*----------------------------------------------------------------------------------------------*)
(* ViewUsers().  Read only.                                                                      *)
(*                                                                                               *)
(* SELECT * FROM USERS.  Modelled as a full scan of the uId domain, present or absent, so that a  *)
(* concurrent registration is a phantom anti-dependency.                                          *)
(*----------------------------------------------------------------------------------------------*)
ViewUsersProgram(req, snap) ==
    [ reads |-> {UserKey(x) : x \in UIds}, writes |-> {} ]

(*----------------------------------------------------------------------------------------------*)
(* StoreBid(iid, val).                                                                           *)
(*                                                                                               *)
(* INSERT INTO BIDS (new bId, iid, val); SELECT nbids FROM ITEMS WHERE iId = iid; UPDATE ITEMS    *)
(* SET nbids = n + 1.  The BIDS insert uses a fresh key per transaction and is never read, so it  *)
(* adds no dependency edge; it is kept only for fidelity to the schema.                           *)
(*                                                                                               *)
(* This is the read-modify-write on ITEMS.nbids that ties StoreBid to itself: two concurrent      *)
(* StoreBids on the same item both read the same committed nbids and both write nbids + 1, so     *)
(* First-Committer-Wins aborts one of them.  The read is of the begin snapshot, so the write      *)
(* value is `n + 1` for the snapshot's `n`, not for whatever committed meanwhile.                 *)
(*----------------------------------------------------------------------------------------------*)
StoreBidProgram(tid, req, snap) ==
    [ reads  |-> {ItemKey(req.iid)},
      writes |-> {[type |-> "write", key |-> BidKey(tid), val |-> Tag],
                  [type |-> "write", key |-> ItemKey(req.iid),
                   val  |-> snap[ItemKey(req.iid)] + 1]} ]

(*----------------------------------------------------------------------------------------------*)
(* ViewItem(iid).  Read only.                                                                    *)
(*                                                                                               *)
(* SELECT * FROM ITEMS WHERE iId = iid.  `desc` is dropped (never written anywhere), so this is   *)
(* a read of ITEMS(iid).nbids.  This is the transaction whose anti-dependency on StoreBid is the  *)
(* rw edge a cycle would need twice in a row; structurally it cannot get one, which is the reason *)
(* StoreBid + ViewItem is robust.                                                                 *)
(*----------------------------------------------------------------------------------------------*)
ViewItemProgram(req, snap) ==
    [ reads |-> {ItemKey(req.iid)}, writes |-> {} ]

(**************************************************************************************************)
(* The set of requests a client may submit, and the expansion of a request to a body.             *)
(**************************************************************************************************)

Requests ==
    (IF "RegUser" \in EnabledTxnTypes
       THEN [type : {"RegUser"}, uid : UIds, name : NIds] ELSE {}) \cup
    (IF "ViewUsers" \in EnabledTxnTypes
       THEN [type : {"ViewUsers"}] ELSE {}) \cup
    (IF "StoreBid" \in EnabledTxnTypes
       THEN [type : {"StoreBid"}, iid : IIds] ELSE {}) \cup
    (IF "ViewItem" \in EnabledTxnTypes
       THEN [type : {"ViewItem"}, iid : IIds] ELSE {})

\* A request may be blocked by the model's semantics rather than its bounds.  RegUser's
\* uniqueness check (SELECT ... WHERE name = uname) is evaluated against the begin snapshot; if it
\* would find a match the transaction aborts, and since aborted transactions are elided we simply
\* do not run it.  It may also not reuse a uId that already names a committed row.
ReqEnabled(req, snap) ==
    IF req.type = "RegUser"
    THEN /\ ~RowExists(snap, UserKey(req.uid))
         /\ \A x \in UIds : snap[UserKey(x)] # req.name
    ELSE TRUE

ProgramFor(tid, req, snap) ==
    CASE req.type = "RegUser"   -> RegUserProgram(req, snap)
      [] req.type = "ViewUsers" -> ViewUsersProgram(req, snap)
      [] req.type = "StoreBid"  -> StoreBidProgram(tid, req, snap)
      [] req.type = "ViewItem"  -> ViewItemProgram(req, snap)

----------------------------------------------------------------------------------------------------

(**************************************************************************************************)
(*                                                                                                *)
(* Initial state                                                                                  *)
(*                                                                                                *)
(* A freshly loaded auction database: ITEMS exist with nbids = 0; USERS and BIDS are empty.       *)
(*                                                                                                *)
(**************************************************************************************************)

InitRow(k) ==
    CASE k.tbl = "ITEM" -> 0
      [] OTHER          -> Empty

InitStore == [k \in Keys |-> InitRow(k)]

Init ==
    /\ clock        = 0
    /\ runningTxns  = {}
    /\ txnHistory   = <<>>
    /\ dataStore    = InitStore
    /\ txnSnapshots = [t \in TxnIds |-> Empty]
    /\ txnReq       = [t \in TxnIds |-> Empty]
    /\ txnProg      = [t \in TxnIds |-> Empty]

----------------------------------------------------------------------------------------------------

(**************************************************************************************************)
(*                                                                                                *)
(* Actions                                                                                        *)
(*                                                                                                *)
(* `StartAndRun` begins a transaction and records its whole body as a single event.  Commit and   *)
(* abort are separate steps.                                                                      *)
(*                                                                                                *)
(**************************************************************************************************)

Unused(tid) == ~\E op \in Range(txnHistory) : op.txnId = tid

\* Fold a body's writes into a snapshot, giving the transaction's final snapshot.  Each key is
\* written at most once by a body, so there is no last-writer question.
ApplyWrites(snap, W) ==
    LET WK == {w.key : w \in W}
    IN [k \in DOMAIN snap \cup WK |->
            IF k \in WK THEN (CHOOSE w \in W : w.key = k).val ELSE snap[k]]

StartAndRun(tid, req) ==
    /\ Unused(tid)
    /\ ReqEnabled(req, dataStore)
    /\ LET prog    == ProgramFor(tid, req, dataStore)
           beginOp == [type |-> "begin", txnId |-> tid, time |-> clock + 1]
           bodyOp  == [type |-> "body",  txnId |-> tid, reads |-> prog.reads, writes |-> prog.writes]
       IN /\ txnHistory'   = txnHistory \o <<beginOp, bodyOp>>
          /\ txnSnapshots' = [txnSnapshots EXCEPT ![tid] = ApplyWrites(dataStore, prog.writes)]
          /\ txnProg'      = [txnProg EXCEPT ![tid] = prog]
    /\ runningTxns' = runningTxns \cup {[id |-> tid, startTime |-> clock + 1, commitTime |-> Empty]}
    /\ clock' = clock + 1
    /\ txnReq' = [txnReq EXCEPT ![tid] = req]
    /\ UNCHANGED <<dataStore>>

\* The keys a transaction has written, read off its body event.
KeysWrittenByTxn(t, h) ==
    {k \in Keys : \E op \in Range(h) : op.txnId = t /\ op.type = "body" /\ \E w \in op.writes : w.key = k}

(*----------------------------------------------------------------------------------------------*)
(* First-Committer-Wins: a transaction may commit only if no transaction that started after it   *)
(* began has already committed a write to a key it intends to write.                             *)
(*----------------------------------------------------------------------------------------------*)
TxnCanCommit(txnId) ==
    \E txn \in runningTxns :
        /\ txn.id = txnId
        /\ ~\E op \in Range(txnHistory) :
            /\ op.type = "commit"
            /\ op.time > txn.startTime
            /\ KeysWrittenByTxn(txnId, txnHistory) \cap op.updatedKeys /= {}

CommitTxn(txnId) ==
    /\ txnId \in {txn.id : txn \in runningTxns}
    \* Must not be a no-op transaction.
    /\ txnProg[txnId] /= Empty
    /\ (txnProg[txnId].reads \cup WriteKeysOf(txnProg[txnId])) /= {}
    /\ TxnCanCommit(txnId)
    /\ LET commitOp == [type        |-> "commit",
                        txnId       |-> txnId,
                        time        |-> clock + 1,
                        updatedKeys |-> KeysWrittenByTxn(txnId, txnHistory)] IN
       txnHistory' = Append(txnHistory, commitOp)
    /\ dataStore' = [k \in Keys |-> IF k \in KeysWrittenByTxn(txnId, txnHistory)
                                        THEN txnSnapshots[txnId][k]
                                        ELSE dataStore[k]]
    /\ runningTxns' = {r \in runningTxns : r.id # txnId}
    /\ clock' = clock + 1
    /\ UNCHANGED <<txnSnapshots, txnReq, txnProg>>

AbortTxn(txnId) ==
    /\ txnId \in {txn.id : txn \in runningTxns}
    /\ txnProg[txnId] /= Empty
    /\ (txnProg[txnId].reads \cup WriteKeysOf(txnProg[txnId])) /= {}
    /\ ~TxnCanCommit(txnId)
    /\ LET abortOp == [type |-> "abort", txnId |-> txnId, time |-> clock + 1] IN
       txnHistory' = Append(txnHistory, abortOp)
    /\ runningTxns' = {r \in runningTxns : r.id # txnId}
    /\ clock' = clock + 1
    /\ UNCHANGED <<dataStore, txnSnapshots, txnReq, txnProg>>

AllTxnsDone == \A tid \in TxnIds :
    \/ tid \in CommittedTxns(txnHistory) \cup AbortedTxns(txnHistory)
    \/ ~\E req \in Requests : Unused(tid) /\ ReqEnabled(req, dataStore)

Next ==
    \/ \E tid \in TxnIds, req \in Requests : StartAndRun(tid, req)
    \/ \E tid \in TxnIds : CommitTxn(tid)
    \/ \E tid \in TxnIds : AbortTxn(tid)
    \/ (AllTxnsDone /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

----------------------------------------------------------------------------------------------------

(**************************************************************************************************)
(*                                                                                                *)
(* The multi-version serialization graph                                                          *)
(*                                                                                                *)
(* An edge T1 -> T2 between committed transactions when:                                          *)
(*   ww  T1 writes a key T2 also writes (so T1 committed first).                                  *)
(*   wr  T1 writes a key T2 reads, and T1 committed before T2 began.                              *)
(*   rw  T1 reads a key T2 writes, and T1 began before T2 committed.                              *)
(*                                                                                                *)
(**************************************************************************************************)

BeginOp(h, t)  == CHOOSE op \in Range(h) : op.txnId = t /\ op.type = "begin"
CommitOp(h, t) == CHOOSE op \in Range(h) : op.txnId = t /\ op.type = "commit"

ReadsKey(h, t, k)  == \E op \in Range(h) : op.txnId = t /\ op.type = "body" /\ k \in op.reads
WritesKey(h, t, k) == \E op \in Range(h) : op.txnId = t /\ op.type = "body" /\
                          \E w \in op.writes : w.key = k

WWDependency(h, t1, t2) ==
    (\E k \in Keys : WritesKey(h, t1, k) /\ WritesKey(h, t2, k))
    /\ CommitOp(h, t1).time < CommitOp(h, t2).time

WRDependency(h, t1, t2) ==
    (\E k \in Keys : WritesKey(h, t1, k) /\ ReadsKey(h, t2, k))
    /\ CommitOp(h, t1).time < BeginOp(h, t2).time

RWDependency(h, t1, t2) ==
    (\E k \in Keys : ReadsKey(h, t1, k) /\ WritesKey(h, t2, k))
    /\ BeginOp(h, t1).time < CommitOp(h, t2).time

SerializationGraph(h) ==
    LET CT == CommittedTxns(h) IN
    {e \in (CT \X CT) :
        /\ e[1] /= e[2]
        /\ \/ WWDependency(h, e[1], e[2])
           \/ WRDependency(h, e[1], e[2])
           \/ RWDependency(h, e[1], e[2])}

GraphNodes(edges) == {e[1] : e \in edges} \cup {e[2] : e \in edges}

\* The set of all paths of a given graph, i.e. all non-empty sequences of nodes whose consecutive
\* elements are connected by an edge.  Path length is bounded by the number of nodes plus one,
\* which keeps the set finite without losing the ability to detect a cycle.
Paths(edges) ==
    LET nodes == GraphNodes(edges)
        maxLen == Cardinality(nodes) + 1
    IN  {p \in UNION {[1..n -> nodes] : n \in 1..maxLen} :
            \A i \in 1..(Len(p)-1) : <<p[i], p[i+1]>> \in edges}

IsCycleViaPath(edges) == \E p \in Paths(edges) : Len(p) > 1 /\ p[1] = p[Len(p)]

IsConflictSerializableViaPath(h) == ~IsCycleViaPath(SerializationGraph(h))

SerializableViaPath == IsConflictSerializableViaPath(txnHistory)

----------------------------------------------------------------------------------------------------

TypeOK ==
    /\ clock \in Nat
    /\ DOMAIN dataStore = Keys
    /\ \A i \in IIds : dataStore[ItemKey(i)] \in 0..MaxNbids
    /\ \A u \in UIds : dataStore[UserKey(u)] \in NIds \cup {Empty}
    /\ \A t \in TxnIds : dataStore[BidKey(t)] \in {Empty, Tag}
    /\ runningTxns \subseteq [id : TxnIds, startTime : Nat, commitTime : Nat \cup {Empty}]
    /\ txnReq \in [TxnIds -> Requests \cup {Empty}]
    /\ DOMAIN txnProg = TxnIds
    /\ \A t \in TxnIds : txnProg[t] = Empty \/ IsBody(txnProg[t])

(**************************************************************************************************)
(* COVERAGE CHECKS.  These are meant to FAIL.  Run them as invariants to confirm that the model   *)
(* is not vacuously serializable because nothing interesting ever happens.  Each one failing      *)
(* means TLC found a behaviour reaching that situation.                                           *)
(**************************************************************************************************)
CommittedCount == Cardinality(CommittedTxns(txnHistory))

Cov_AllTxnsCommit  == CommittedCount < NumTxns
Cov_SomeTxnAborts  == AbortedTxns(txnHistory) = {}
Cov_ConcurrentTxns == Cardinality(runningTxns) < 2

Cov_TypeCommits(ty) == ~\E t \in CommittedTxns(txnHistory) :
                            txnReq[t] # Empty /\ txnReq[t].type = ty

\* An rw-anti-dependency between two committed transactions is the ingredient every SI anomaly
\* needs.  If this never fails, the model is too small to say anything about serializability.
Cov_RWEdgeExists ==
    ~\E t1, t2 \in CommittedTxns(txnHistory) :
        t1 # t2 /\ RWDependency(txnHistory, t1, t2)

=====================================================================================================
