------------------------------------ MODULE Auction ------------------------------------
(**************************************************************************************************)
(*                                                                                                *)
(* A TLA+ model of the auction application from Bernardi & Gotsman, "Robustness against           *)
(* Consistency Models with Atomic Visibility" (CONCUR 2016), running on top of a key-value store  *)
(* that provides SNAPSHOT ISOLATION.                                                              *)
(*                                                                                                *)
(* The snapshot isolation layer is NOT re-implemented here.  It is the unmodified                 *)
(* `SnapshotIsolation` module, instantiated the same way `TPCC` does.  All of the                  *)
(* subtle parts of SI -- the begin snapshot, read-your-own-writes, the First-Committer-Wins       *)
(* write-conflict rule, and the multi-version serialization graph (MVSG) used to decide conflict  *)
(* serializability -- come from that module verbatim.  This module only adds a *workload*: it     *)
(* constrains which keys each transaction reads and writes, and in what order, so that the        *)
(* transactions are the four programs of the paper's running example rather than arbitrary ones.  *)
(*                                                                                                *)
(* THE QUESTION                                                                                   *)
(*                                                                                                *)
(*     Is every history produced by running the auction programs under snapshot isolation          *)
(*     conflict serializable?  (invariant `Serializable`)                                         *)
(*                                                                                                *)
(* The answer depends on the transaction mix, and the paper's own two headline analyses are the   *)
(* two sides of it:                                                                               *)
(*                                                                                                *)
(*   * StoreBid + ViewItem -- ROBUST.  §2 and §6 prove that every PSI (hence every SI) execution   *)
(*     of these two programs has a serializable history.  The reason is structural: no cycle in     *)
(*     the MVSG carries two consecutive rw-anti-dependency edges.  (Individual rw edges abound --   *)
(*     every ViewItem -> StoreBid edge, and also StoreBid -> StoreBid between two serialized        *)
(*     StoreBids -- but they never line up twice around a cycle.  Cf. `NoDangerousCycle`.)          *)
(*     Config `auction-robust`.                                                                    *)
(*                                                                                                *)
(*   * RegUser -- NOT ROBUST.  Two concurrent RegUsers registering the same nickname miss each     *)
(*     other's uniqueness check and both insert, producing the write skew of Figure 2(d).  That    *)
(*     is an SI-critical cycle, hence a genuinely non-serializable history.  Config               *)
(*     `auction-reguser`.                                                                         *)
(*                                                                                                *)
(* GRANULARITY (why this module has no `ColumnGranularity` knob)                                  *)
(*                                                                                                *)
(* TPCC_TLAPS carries a `ColumnGranularity` constant because at row granularity two TPC-C         *)
(* transactions that share a row but touch disjoint columns manufacture a false dependency edge.   *)
(* No such pair exists in the auction schema: the only row with several fields is ITEMS(desc,      *)
(* nbids), and while ViewItem reads `desc`, no program ever writes it; every other table is        *)
(* effectively single-column.  Row and column granularity therefore induce the same dependency     *)
(* graph here, so the knob would be decorative and is omitted.  Predicate reads are still          *)
(* modelled as range scans (below), which is the one granularity choice that does matter.          *)
(*                                                                                                *)
(**************************************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences, TLC

(**************************************************************************************************)
(* Scale factors.  Keep them tiny: the interesting structure of the auction shows up at two        *)
(* items, two users and two or three transactions.                                                 *)
(**************************************************************************************************)

CONSTANT NumItems      \* rows in ITEMS
CONSTANT NumUsers      \* rows USERS can ever hold (the uId domain)
CONSTANT NumNames      \* distinct nicknames a RegUser may request
CONSTANT NumTxns       \* how many transactions may run in a behaviour

\* Which of the four auction programs are allowed to run.  Subset of
\* {"RegUser", "ViewUsers", "StoreBid", "ViewItem"}.
CONSTANT EnabledTxnTypes

\* The "does not exist" / NULL value.  Also the `Empty` of the snapshot isolation module.
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
ASSUME NumTxns \in Nat

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
(*   * USERS(uId).name -- read by RegUser's uniqueness check and by ViewUsers; its value is the     *)
(*     only thing that decides whether RegUser inserts.  Stored exactly.                          *)
(*   * ITEMS(iId).nbids -- read-modify-written by StoreBid and read by ViewItem.  Stored exactly,  *)
(*     because it is what makes the lost-update / write-conflict behaviour observable, and it     *)
(*     supports the `BidCountsConsistent` coherence check.                                        *)
(*   * ITEMS(iId).desc -- never read or written by any program; dropped.                          *)
(*   * BIDS(bId, iId, val) -- StoreBid's insert-only output.  No program reads BIDS, and each      *)
(*     StoreBid uses a fresh bId, so it can never conflict.  Modelled with one fresh key per      *)
(*     transaction (the same aggregation TPCC_TLAPS makes for HISTORY).                           *)
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
(* Variables.  The first five are the variables of the snapshot isolation module (bound by name    *)
(* when we INSTANCE it).  The last two are bookkeeping for the workload layer.                     *)
(**************************************************************************************************)

VARIABLE clock          \* SI: ticks on every begin and commit
VARIABLE runningTxns    \* SI: set of in-flight transactions
VARIABLE txnHistory     \* SI: the linear event history, the thing we check serializability of
VARIABLE dataStore      \* SI: the committed key-value store
VARIABLE txnSnapshots   \* SI: per-transaction snapshot of the store

VARIABLE txnReq         \* txnId -> the auction request this transaction is executing
VARIABLE txnProg        \* txnId -> the sequence of read/write ops that request expands to

siVars == <<clock, runningTxns, txnSnapshots, dataStore, txnHistory>>
wlVars == <<txnReq, txnProg>>
vars   == <<clock, runningTxns, txnSnapshots, dataStore, txnHistory, txnReq, txnProg>>

(**************************************************************************************************)
(* Instantiate the snapshot isolation specification.  From here on, `SI!Foo` is Foo as defined in *)
(* SnapshotIsolationTLAPS.tla, operating on the variables declared above.                          *)
(**************************************************************************************************)

SI == INSTANCE SnapshotIsolation WITH
    txnIds <- TxnIds,
    keys   <- Keys,
    values <- NIds \cup (0..MaxNbids) \cup {Tag},   \* only used by that module's (unchecked) type invariant
    Empty  <- Empty

----------------------------------------------------------------------------------------------------

(**************************************************************************************************)
(* Sequence helpers.  TLAPS rejects recursive *operators*, so each is a recursive *function*,       *)
(* indexed by position (or by remaining cardinality for `SeqOf`).  Copied from TPCC_TLAPS.          *)
(**************************************************************************************************)

Min(S) == CHOOSE x \in S : \A y \in S : x =< y

\* A finite set of naturals as an ascending sequence.
SeqOf(S) ==
    LET n == Cardinality(S)
        g[i \in 0..n] == IF i = 0 THEN S ELSE g[i-1] \ {Min(g[i-1])}
        f[i \in 0..n] == IF i = 0 THEN <<>> ELSE f[i-1] \o <<Min(g[i-1])>>
    IN f[n]

\* Concatenation of all elements of a sequence of sequences.
Flatten(s) ==
    LET f[i \in 0..Len(s)] == IF i = 0 THEN <<>> ELSE f[i-1] \o s[i]
    IN f[Len(s)]

\* Apply `f` to each element of the ascending sequence of `ids`, concatenating the results.
ConcatOver(f(_), ids) == LET s == SeqOf(ids) IN Flatten([i \in 1..Len(s) |-> f(s[i])])

\* Transitive closure of a graph given as a set of edges, by bounded iteration (a recursive
\* function, which TLAPS accepts).  Any path that revisits a node can be shortened, so every
\* reachability fact is witnessed by a simple path of at most Cardinality(Nodes) edges.
\* Every node with an incident edge.
Nodes(edges) == {e[1] : e \in edges} \cup {e[2] : e \in edges}

TransitiveClosure(edges) ==
    LET V == Nodes(edges)
        n == Cardinality(V)
        R[i \in 0..n] ==
            IF i = 0
              THEN edges
              ELSE R[i-1] \cup {e \in V \X V :
                       \E y \in V : <<e[1], y>> \in R[i-1] /\ <<y, e[2]>> \in edges}
    IN R[n]

----------------------------------------------------------------------------------------------------

(**************************************************************************************************)
(* Statements.  At the auction's (single-column) object granularity a statement is just a read or  *)
(* a write of one key, so each expands to a one-element program.                                   *)
(**************************************************************************************************)

Rd(snap, k) == << [type |-> "read",  key |-> k, val |-> snap[k]] >>
Wr(k, v)    == << [type |-> "write", key |-> k, val |-> v] >>

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
(*                                                                                                *)
(* SELECT name FROM USERS WHERE name = uname; if a row matches, abort; else INSERT a new row      *)
(* with a fresh uId and this nickname.                                                            *)
(*                                                                                                *)
(* The conditional abort is modelled by *not running* an instance whose uniqueness check would    *)
(* fail against its begin snapshot (see `ReqEnabled`).  Aborted transactions are elided from the  *)
(* histories the paper reasons about, so omitting them does not change the set of committed       *)
(* histories or the MVSG built over them -- while still requiring the scan reads, which do leave  *)
(* the anti-dependency edges.  The uId is a client-supplied fresh id; inserting a taken uId would *)
(* be a write-write conflict, handled by First-Committer-Wins.                                    *)
(*                                                                                                *)
(* NOTE: the paper's RegUser is the source of the write skew.  Two concurrent instances with the  *)
(* same uname both scan, both see no match, and both insert rows with different uIds -- a cycle   *)
(* of the form RegUser --rw--> RegUser --rw--> RegUser that no serial order can produce.           *)
(*----------------------------------------------------------------------------------------------*)
RegUserProgram(req, snap) ==
    LET RdUser(x) == Rd(snap, UserKey(x))
    IN    ConcatOver(RdUser, UIds)
       \o Wr(UserKey(req.uid), req.name)

(*----------------------------------------------------------------------------------------------*)
(* ViewUsers().  Read only.                                                                      *)
(*                                                                                                *)
(* SELECT * FROM USERS.  Modelled as a full scan of the uId domain, present or absent, so that a  *)
(* concurrent registration is a phantom anti-dependency.                                          *)
(*----------------------------------------------------------------------------------------------*)
ViewUsersProgram(req, snap) ==
    LET RdUser(x) == Rd(snap, UserKey(x))
    IN ConcatOver(RdUser, UIds)

(*----------------------------------------------------------------------------------------------*)
(* StoreBid(iid, val).                                                                            *)
(*                                                                                                *)
(* INSERT INTO BIDS (new bId, iid, val); SELECT nbids FROM ITEMS WHERE iId = iid; UPDATE ITEMS    *)
(* SET nbids = n + 1.  The BIDS insert uses a fresh key per transaction and is never read, so it  *)
(* adds no dependency edge; it is kept only for fidelity to the schema.                           *)
(*                                                                                                *)
(* This is the read-modify-write on ITEMS.nbids that ties StoreBid to itself: two concurrent      *)
(* StoreBids on the same item both read the same committed nbids and both write nbids + 1, so     *)
(* First-Committer-Wins aborts one of them.  The read is of the begin snapshot, so the write      *)
(* value is `n + 1` for the snapshot's `n`, not for whatever committed meanwhile.                 *)
(*----------------------------------------------------------------------------------------------*)
StoreBidProgram(tid, req, snap) ==
    LET i == req.iid
    IN    Wr(BidKey(tid), Tag)
       \o Rd(snap, ItemKey(i))
       \o Wr(ItemKey(i), snap[ItemKey(i)] + 1)

(*----------------------------------------------------------------------------------------------*)
(* ViewItem(iid).  Read only.                                                                     *)
(*                                                                                                *)
(* SELECT * FROM ITEMS WHERE iId = iid.  `desc` is dropped (never written anywhere), so this is   *)
(* a read of ITEMS(iid).nbids.  This is the transaction whose anti-dependency on StoreBid is the  *)
(* rw edge a cycle would need twice in a row; structurally it cannot get one, which is the reason *)
(* StoreBid + ViewItem is robust.                                                                 *)
(*----------------------------------------------------------------------------------------------*)
ViewItemProgram(req, snap) ==
    Rd(snap, ItemKey(req.iid))

(**************************************************************************************************)
(* The set of requests a client may submit, and the expansion of a request to a program.           *)
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
    /\ txnProg      = [t \in TxnIds |-> <<>>]

----------------------------------------------------------------------------------------------------

(**************************************************************************************************)
(*                                                                                                *)
(* Actions                                                                                        *)
(*                                                                                                *)
(* COARSE-GRAINED only (`Next`): a transaction begins and runs its whole body in one step, then   *)
(* commits or aborts.  Collapsing the body is exact, not an approximation.  Under SI a             *)
(* transaction's reads are answered entirely from its begin snapshot plus its own prior writes,    *)
(* and its writes are invisible to everyone else until commit, so the position of a body           *)
(* operation inside [begin, commit] is unobservable, and the MVSG is built only from begin times,  *)
(* commit times, and per-transaction read/write key sets -- never from body interleaving.  The one *)
(* premise this needs is that no program reads a key it has already written, which is checked     *)
(* (not assumed) by `NoReadAfterWrite`.                                                           *)
(*                                                                                                *)
(**************************************************************************************************)

Unused(tid) == ~\E op \in SI!Range(txnHistory) : op.txnId = tid

\* Fold a program's writes into a snapshot, giving the transaction's final snapshot.
ApplyWrites(snap, ops) ==
    LET f[i \in 0..Len(ops)] ==
          IF i = 0
            THEN snap
            ELSE IF ops[i].type = "write"
                   THEN [f[i-1] EXCEPT ![ops[i].key] = ops[i].val]
                   ELSE f[i-1]
    IN f[Len(ops)]

(*----------------------------------------------------------------------------------------------*)
(* Begin a transaction and run its whole body in one step.                                         *)
(*                                                                                              *)
(* The begin half is exactly `SI!StartTxn` -- snapshot the committed store, append a `begin`      *)
(* event, join the running set, tick the clock.  It is inlined only because the body's events     *)
(* must be appended to `txnHistory` in the same step.                                             *)
(*----------------------------------------------------------------------------------------------*)
StartAndRun(tid, req) ==
    /\ Unused(tid)
    /\ ReqEnabled(req, dataStore)
    /\ LET prog    == ProgramFor(tid, req, dataStore)
           beginOp == [type |-> "begin", txnId |-> tid, time |-> clock + 1]
           events  == [i \in 1..Len(prog) |-> prog[i] @@ [txnId |-> tid]]
       IN /\ txnHistory'   = txnHistory \o <<beginOp>> \o events
          /\ txnSnapshots' = [txnSnapshots EXCEPT ![tid] = ApplyWrites(dataStore, prog)]
          /\ txnProg'      = [txnProg EXCEPT ![tid] = prog]
    /\ runningTxns' = runningTxns \cup {[id |-> tid, startTime |-> clock + 1, commitTime |-> Empty]}
    /\ clock' = clock + 1
    /\ txnReq' = [txnReq EXCEPT ![tid] = req]
    /\ UNCHANGED <<dataStore>>

(*----------------------------------------------------------------------------------------------*)
(* Commit / abort are `SI!CommitTxn` and `SI!AbortTxn` verbatim: First-Committer-Wins decides,    *)
(* and a transaction aborts exactly when a concurrent transaction already committed a write to    *)
(* a key it intends to write.                                                                     *)
(*----------------------------------------------------------------------------------------------*)
CommitTxn(tid) == SI!CommitTxn(tid) /\ UNCHANGED wlVars
AbortTxn(tid)  == SI!AbortTxn(tid)  /\ UNCHANGED wlVars

AllTxnsDone == \A tid \in TxnIds :
    \/ tid \in SI!CommittedTxns(txnHistory) \cup SI!AbortedTxns(txnHistory)
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
(* Correctness properties                                                                         *)
(*                                                                                                *)
(**************************************************************************************************)

(**************************************************************************************************)
(* THE MAIN QUESTION.  Is the history this auction workload produces under snapshot isolation      *)
(* conflict serializable?  `SI!IsConflictSerializable` builds the multi-version serialization      *)
(* graph over committed transactions (ww, wr and rw edges) and asks whether it is acyclic.         *)
(**************************************************************************************************)
\* Serializable == SI!IsConflictSerializable(txnHistory)

SerializableViaPath == SI!IsConflictSerializableViaPath(txnHistory)


TypeOK ==
    /\ clock \in Nat
    /\ DOMAIN dataStore = Keys
    /\ \A i \in IIds : dataStore[ItemKey(i)] \in 0..MaxNbids
    /\ \A u \in UIds : dataStore[UserKey(u)] \in NIds \cup {Empty}
    /\ \A t \in TxnIds : dataStore[BidKey(t)] \in {Empty, Tag}
    /\ runningTxns \subseteq [id : TxnIds, startTime : Nat, commitTime : Nat \cup {Empty}]
    /\ txnReq \in [TxnIds -> Requests \cup {Empty}]

(**************************************************************************************************)
(* COVERAGE CHECKS.  These are meant to FAIL.  Run them as invariants to confirm that the model   *)
(* is not vacuously serializable because nothing interesting ever happens.  Each one failing      *)
(* means TLC found a behaviour reaching that situation.                                           *)
(**************************************************************************************************)
CommittedCount == Cardinality(SI!CommittedTxns(txnHistory))

Cov_AllTxnsCommit  == CommittedCount < NumTxns
Cov_SomeTxnAborts  == SI!AbortedTxns(txnHistory) = {}
Cov_ConcurrentTxns == Cardinality(runningTxns) < 2

Cov_TypeCommits(ty) == ~\E t \in SI!CommittedTxns(txnHistory) :
                            txnReq[t] # Empty /\ txnReq[t].type = ty

\* An rw-anti-dependency between two committed transactions is the ingredient every SI anomaly
\* needs.  If this never fails, the model is too small to say anything about serializability.
Cov_RWEdgeExists ==
    ~\E t1, t2 \in SI!CommittedTxns(txnHistory) :
        t1 # t2 /\ SI!RWDependency(txnHistory, t1, t2)

=====================================================================================================
