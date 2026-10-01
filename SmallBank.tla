----------------------------------- MODULE SmallBank -----------------------------------
(**************************************************************************************************)
(*                                                                                                *)
(* A TLA+ model of the SmallBank benchmark of Alomari, Cahill, Fekete & Röhm, "The Cost of         *)
(* Serializability on Platforms That Use Snapshot Isolation" (ICDE 2008), running on top of a      *)
(* key-value store that provides SNAPSHOT ISOLATION.                                              *)
(*                                                                                                *)
(* The snapshot isolation layer is not modelled here.  It is provided by instantiating the        *)
(* `SnapshotIsolation` module, which owns the store state -- the committed data store, the         *)
(* per-transaction snapshots, the clock, the set of running transactions, and the linear event     *)
(* history -- together with the begin / commit / abort actions, read-your-own-writes, the          *)
(* First-Committer-Wins rule, and the multi-version serialization graph (MVSG) used to decide      *)
(* conflict serializability.  This module supplies only the *workload*: it constrains which keys   *)
(* each transaction reads and writes, so that the transactions are the five SmallBank programs     *)
(* rather than arbitrary ones.                                                                    *)
(*                                                                                                *)
(* The two layers are coupled through the transaction body.  `SnapshotIsolation.StartAndRun`       *)
(* takes a body (a read key set and a write set) as a parameter; this module computes that body    *)
(* from a SmallBank request and the current committed store via `ProgramFor`, then hands it to the *)
(* instantiated action.                                                                           *)
(*                                                                                                *)
(* THE QUESTION                                                                                   *)
(*                                                                                                *)
(*     Is every history produced by running the SmallBank programs under snapshot isolation       *)
(*     conflict serializable?  (invariant `SerializableViaPath`)                                  *)
(*                                                                                                *)
(* SmallBank was designed to be NOT robust, and the answer again depends on the mix.  Following    *)
(* the static dependency graph analysis of the paper, an rw-anti-dependency edge T1 --rw--> T2 is  *)
(* "vulnerable" (can occur between concurrent transactions) only if T1 reads a key that T2 writes  *)
(* and T1 does NOT also write it -- otherwise First-Committer-Wins forces the two apart.  In       *)
(* SmallBank there are exactly two sources of such edges:                                         *)
(*                                                                                                *)
(*   * Balance, which is read-only, has a vulnerable edge to every updater.                       *)
(*   * WriteCheck reads SAVINGS(c) but writes only CHECKING(c), so it has a vulnerable edge to    *)
(*     TransactSavings and Amalgamate, the two programs that write SAVINGS.                       *)
(*                                                                                                *)
(* Every non-serializable SI history contains a "dangerous structure" -- two consecutive          *)
(* vulnerable edges -- and the only way to chain two here is                                      *)
(*                                                                                                *)
(*     Balance --rw--> WriteCheck --rw--> {TransactSavings | Amalgamate}                          *)
(*                                                                                                *)
(* with WriteCheck as the pivot.  This is precisely the read-only transaction anomaly of Fekete,  *)
(* O'Neil & O'Neil: a Balance that observes TransactSavings' deposit but not the WriteCheck that   *)
(* was charged an overdraft penalty because it did not see that deposit.  So:                     *)
(*                                                                                                *)
(*   * any mix without WriteCheck -- ROBUST.  Every updater reads only keys it writes (ACCOUNT is  *)
(*     never written), so only Balance emits vulnerable edges and they can never be adjacent.      *)
(*     Config `smallbank-robust`.                                                                 *)
(*   * any mix without Balance -- also ROBUST.  WriteCheck's vulnerable edges have nowhere to come *)
(*     from: every program that writes CHECKING also reads it.  Config `smallbank-nobalance`.      *)
(*   * Balance + WriteCheck + TransactSavings -- NOT ROBUST.  The read-only anomaly above, a       *)
(*     three-transaction cycle.  Config `smallbank-roanomaly`; `smallbank-allmix` runs all five.  *)
(*                                                                                                *)
(* REPRESENTATION: A TRANSACTION BODY IS ONE EVENT                                                *)
(*                                                                                                *)
(* Conflict serializability depends only on each transaction's begin time, commit time, read key  *)
(* set and write key set -- never on the order in which its body operations execute (under SI a   *)
(* transaction's writes are invisible until commit, and its reads see only its begin snapshot, so *)
(* no other transaction observes the body's interleaving).  So the body is recorded as a single   *)
(* event carrying those two sets, rather than as a sequence of individual read/write events.      *)
(* This is the same representation `SnapshotIsolation` uses, which is exactly why a body computed *)
(* here can be passed straight to its `StartAndRun` action.                                       *)
(*                                                                                                *)
(* VALUES                                                                                         *)
(*                                                                                                *)
(* Unlike the auction, no stored value in SmallBank steers *which keys are touched*.  Every       *)
(* program addresses rows by primary key, and its read and write sets are fixed by its arguments. *)
(* The balances decide only *what is written* (WriteCheck's overdraft penalty) and, in some       *)
(* SmallBank variants, whether a program rolls back on a negative balance.  So, as TPCC does for   *)
(* its non-steering columns, every balance write stores a constant tag.  This removes no MVSG      *)
(* edge and keeps the state space finite.  The one consequence: client-initiated rollbacks (e.g.  *)
(* TransactSavings refusing to overdraw) are not represented -- every transaction runs and is      *)
(* aborted only by First-Committer-Wins, as in TPCC.  Since aborted transactions contribute no     *)
(* edges, this can only add committed histories, so a "serializable" verdict stays sound.          *)
(*                                                                                                *)
(* GRANULARITY (why this module has no `ColumnGranularity` knob)                                  *)
(*                                                                                                *)
(* Every SmallBank table has a single non-key column (ACCOUNT.custId, SAVINGS.bal, CHECKING.bal), *)
(* so row and column granularity coincide.  There are no predicate reads either: every access is  *)
(* by primary key, so no range scans are needed for phantoms.                                     *)
(*                                                                                                *)
(**************************************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences, Functions

(**************************************************************************************************)
(* Scale factors.  Keep them tiny: the read-only anomaly needs one customer and three             *)
(* transactions; Amalgamate needs two customers.                                                  *)
(**************************************************************************************************)

CONSTANT NumCustomers  \* customers, each with one ACCOUNT, SAVINGS and CHECKING row
CONSTANT NumTxns       \* how many transactions may run in a behaviour

\* Which of the five SmallBank programs are allowed to run.  Subset of
\* {"Balance", "DepositChecking", "TransactSavings", "Amalgamate", "WriteCheck"}.
CONSTANT EnabledTxnTypes

\* The "does not exist" / NULL value.
CONSTANT Empty

CIds   == 1..NumCustomers
TxnIds == 1..NumTxns

Tag == "v"

AllTxnTypes == {"Balance", "DepositChecking", "TransactSavings", "Amalgamate", "WriteCheck"}

ASSUME EnabledTxnTypes \subseteq AllTxnTypes
ASSUME NumTxnsNat == NumTxns \in Nat

----------------------------------------------------------------------------------------------------

(**************************************************************************************************)
(*                                                                                                *)
(* The schema.                                                                                    *)
(*                                                                                                *)
(*     ACCOUNT(name, custId)                                                                      *)
(*     SAVINGS(custId, bal)                                                                       *)
(*     CHECKING(custId, bal)                                                                      *)
(*                                                                                                *)
(* Every program first resolves a customer name to a custId through ACCOUNT, then works on that   *)
(* customer's SAVINGS and/or CHECKING row.  We identify names with custIds (customer c is named   *)
(* c), so the ACCOUNT lookup is the identity -- but it is still recorded as a read, for fidelity.  *)
(* ACCOUNT is never written by any program, so those reads can never produce an MVSG edge.        *)
(*                                                                                                *)
(**************************************************************************************************)

AccountKey(c)  == [tbl |-> "ACCOUNT",  c |-> c]
SavingsKey(c)  == [tbl |-> "SAVINGS",  c |-> c]
CheckingKey(c) == [tbl |-> "CHECKING", c |-> c]

Keys == {AccountKey(c)  : c \in CIds} \cup
        {SavingsKey(c)  : c \in CIds} \cup
        {CheckingKey(c) : c \in CIds}

\* The value universe handed to `SnapshotIsolation`: an ACCOUNT row stores its custId, a balance
\* row stores the opaque tag.  (Only SANY needs it; the `Bodies` set `SnapshotIsolation` builds
\* from it is never used, since this module always supplies a body explicitly.)
Vals == {Tag, Empty} \cup CIds

----------------------------------------------------------------------------------------------------

(**************************************************************************************************)
(* Variables.                                                                                     *)
(*                                                                                                *)
(* The store variables -- clock, runningTxns, txnHistory, dataStore, txnSnapshots, txnProg -- are *)
(* declared here and shared with the `SnapshotIsolation` instance below by the default same-name   *)
(* substitution.  `txnReq` is this module's own bookkeeping: the SmallBank request each           *)
(* transaction is executing.                                                                      *)
(**************************************************************************************************)

VARIABLE clock          \* ticks on every begin and commit
VARIABLE runningTxns    \* set of in-flight transactions
VARIABLE txnHistory     \* the linear event history, the thing we check serializability of
VARIABLE dataStore      \* the committed key-value store
VARIABLE txnSnapshots   \* per-transaction snapshot of the store
VARIABLE txnProg        \* txnId -> the body this request expands to (reads / writes)
VARIABLE txnReq         \* txnId -> the SmallBank request this transaction is executing

vars == <<clock, runningTxns, txnSnapshots, dataStore, txnHistory, txnReq, txnProg>>

(**************************************************************************************************)
(*                                                                                                *)
(* The backing store: an instantiation of the `SnapshotIsolation` module.                          *)
(*                                                                                                *)
(* This provides the begin / commit / abort actions, the First-Committer-Wins rule, and the        *)
(* multi-version serialization graph used to decide conflict serializability.  Its constants are   *)
(* bound to this module's SmallBank schema; its variables are the store variables declared above.  *)
(*                                                                                                *)
(**************************************************************************************************)

SI == INSTANCE SnapshotIsolation WITH
        txnIds <- TxnIds,
        keys   <- Keys,
        values <- Vals,
        Empty  <- Empty

(**************************************************************************************************)
(*                                                                                                *)
(* The operations a transaction body consists of.                                                 *)
(*                                                                                                *)
(* A body is a record with two fields: `reads`, the set of keys read, and `writes`, the set of    *)
(* write operations (each a key together with the value written).  This is exactly the shape       *)
(* `SnapshotIsolation` expects (its `BodyType`).                                                  *)
(*                                                                                                *)
(**************************************************************************************************)

\* The value a write may carry is determined by the table it writes.  Only the balance tables are
\* ever written.  Typing it per table keeps every comparison within a single type, which is what
\* TLC requires.
ValsOf(tbl) ==
    CASE tbl = "ACCOUNT"  -> CIds
      [] tbl = "SAVINGS"  -> {Tag}
      [] tbl = "CHECKING" -> {Tag}

IsWriteOp(w) ==
    /\ DOMAIN w = {"type", "key", "val"}
    /\ w.type = "write" /\ w.key \in Keys /\ w.val \in ValsOf(w.key.tbl)

IsBody(B) ==
    /\ DOMAIN B = {"reads", "writes"}
    /\ B.reads \subseteq Keys
    /\ \A w \in B.writes : IsWriteOp(w)

Write(k) == [type |-> "write", key |-> k, val |-> Tag]

----------------------------------------------------------------------------------------------------

(**************************************************************************************************)
(*                                                                                                *)
(* The SmallBank programs.                                                                        *)
(*                                                                                                *)
(* Each takes customer names (here: custIds) and an amount.  The amount only affects the values   *)
(* written, which are abstracted to `Tag` (see VALUES above), so it is not a request field.       *)
(*                                                                                                *)
(**************************************************************************************************)

(*----------------------------------------------------------------------------------------------*)
(* Balance(N).  Read only.                                                                       *)
(*                                                                                               *)
(* SELECT custId FROM ACCOUNT WHERE name = N; SELECT bal FROM SAVINGS WHERE custId = c;           *)
(* SELECT bal FROM CHECKING WHERE custId = c; return the sum.                                     *)
(*                                                                                               *)
(* As a read-only transaction it has a vulnerable rw edge to every updater of either balance.     *)
(* It is the head of the dangerous structure: it can see TransactSavings' deposit while missing   *)
(* the WriteCheck that serialized before it.                                                      *)
(*----------------------------------------------------------------------------------------------*)
BalanceProgram(req, snap) ==
    [ reads  |-> {AccountKey(req.c), SavingsKey(req.c), CheckingKey(req.c)},
      writes |-> {} ]

(*----------------------------------------------------------------------------------------------*)
(* DepositChecking(N, V).                                                                        *)
(*                                                                                               *)
(* Look up c; SELECT bal FROM CHECKING WHERE custId = c; UPDATE CHECKING SET bal = bal + V.       *)
(* A read-modify-write of CHECKING(c): it reads only what it writes.                              *)
(*----------------------------------------------------------------------------------------------*)
DepositCheckingProgram(req, snap) ==
    [ reads  |-> {AccountKey(req.c), CheckingKey(req.c)},
      writes |-> {Write(CheckingKey(req.c))} ]

(*----------------------------------------------------------------------------------------------*)
(* TransactSavings(N, V).                                                                        *)
(*                                                                                               *)
(* Look up c; SELECT bal FROM SAVINGS WHERE custId = c; UPDATE SAVINGS SET bal = bal + V.         *)
(* A read-modify-write of SAVINGS(c): it reads only what it writes.  It is the tail of the        *)
(* dangerous structure, the target of WriteCheck's vulnerable edge.                               *)
(*----------------------------------------------------------------------------------------------*)
TransactSavingsProgram(req, snap) ==
    [ reads  |-> {AccountKey(req.c), SavingsKey(req.c)},
      writes |-> {Write(SavingsKey(req.c))} ]

(*----------------------------------------------------------------------------------------------*)
(* Amalgamate(N1, N2).                                                                           *)
(*                                                                                               *)
(* Look up c1 and c2; read SAVINGS(c1) and CHECKING(c1); zero both; add their total to           *)
(* CHECKING(c2).  Reads exactly the three balance rows it writes.  N1 and N2 must name distinct   *)
(* customers (see `Requests`).                                                                    *)
(*----------------------------------------------------------------------------------------------*)
AmalgamateProgram(req, snap) ==
    [ reads  |-> {AccountKey(req.c1), AccountKey(req.c2),
                  SavingsKey(req.c1), CheckingKey(req.c1), CheckingKey(req.c2)},
      writes |-> {Write(SavingsKey(req.c1)), Write(CheckingKey(req.c1)),
                  Write(CheckingKey(req.c2))} ]

(*----------------------------------------------------------------------------------------------*)
(* WriteCheck(N, V).                                                                             *)
(*                                                                                               *)
(* Look up c; read SAVINGS(c) and CHECKING(c); if their sum is below V, UPDATE CHECKING SET       *)
(* bal = bal - (V + 1) (an overdraft penalty), else bal = bal - V.                                *)
(*                                                                                               *)
(* NOTE: this is the pivot of SmallBank's non-robustness.  It reads SAVINGS(c) to decide the      *)
(* penalty but writes only CHECKING(c), so a concurrent TransactSavings (or Amalgamate) can change *)
(* the savings balance it decided on without any write-write conflict.  The branch itself only    *)
(* chooses the value written, so it is abstracted away; the read of SAVINGS(c) is what matters.   *)
(*----------------------------------------------------------------------------------------------*)
WriteCheckProgram(req, snap) ==
    [ reads  |-> {AccountKey(req.c), SavingsKey(req.c), CheckingKey(req.c)},
      writes |-> {Write(CheckingKey(req.c))} ]

(**************************************************************************************************)
(* The set of requests a client may submit, and the expansion of a request to a body.             *)
(**************************************************************************************************)

Requests ==
    (IF "Balance" \in EnabledTxnTypes
       THEN [type : {"Balance"}, c : CIds] ELSE {}) \cup
    (IF "DepositChecking" \in EnabledTxnTypes
       THEN [type : {"DepositChecking"}, c : CIds] ELSE {}) \cup
    (IF "TransactSavings" \in EnabledTxnTypes
       THEN [type : {"TransactSavings"}, c : CIds] ELSE {}) \cup
    (IF "Amalgamate" \in EnabledTxnTypes
       THEN {r \in [type : {"Amalgamate"}, c1 : CIds, c2 : CIds] : r.c1 # r.c2} ELSE {}) \cup
    (IF "WriteCheck" \in EnabledTxnTypes
       THEN [type : {"WriteCheck"}, c : CIds] ELSE {})

\* No SmallBank request is blocked by the state of the store: every customer exists from the
\* start, and the balance-dependent rollbacks are abstracted away (see VALUES above).  Kept as an
\* explicit hook so the action structure matches `Auction` and `TPCC`.
ReqEnabled(req, snap) == TRUE

ProgramFor(tid, req, snap) ==
    CASE req.type = "Balance"         -> BalanceProgram(req, snap)
      [] req.type = "DepositChecking" -> DepositCheckingProgram(req, snap)
      [] req.type = "TransactSavings" -> TransactSavingsProgram(req, snap)
      [] req.type = "Amalgamate"      -> AmalgamateProgram(req, snap)
      [] req.type = "WriteCheck"      -> WriteCheckProgram(req, snap)

----------------------------------------------------------------------------------------------------

(**************************************************************************************************)
(*                                                                                                *)
(* Initial state                                                                                  *)
(*                                                                                                *)
(* A freshly loaded bank: every customer has an ACCOUNT row and a SAVINGS and CHECKING balance.   *)
(* The store's initial value is workload-specific, so this module supplies it rather than         *)
(* reusing `SnapshotIsolation`'s all-empty `Init`.                                                *)
(*                                                                                                *)
(**************************************************************************************************)

InitRow(k) ==
    CASE k.tbl = "ACCOUNT" -> k.c
      [] OTHER             -> Tag

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
(* These are thin wrappers over `SnapshotIsolation`.  `StartAndRun` picks a SmallBank request,     *)
(* turns it into a body via `ProgramFor`, and hands that body to `SI!StartAndRun`; commit and      *)
(* abort delegate entirely.  The only state this module adds is `txnReq`, which each action must   *)
(* pin.                                                                                           *)
(*                                                                                                *)
(**************************************************************************************************)

Unused(tid) == ~\E op \in Range(txnHistory) : op.txnId = tid

StartAndRun(tid, req) ==
    /\ ReqEnabled(req, dataStore)
    /\ SI!StartAndRun(tid, ProgramFor(tid, req, dataStore))
    /\ txnReq' = [txnReq EXCEPT ![tid] = req]

CommitTxn(tid) ==
    /\ SI!CommitTxn(tid)
    /\ UNCHANGED txnReq

AbortTxn(tid) ==
    /\ SI!AbortTxn(tid)
    /\ UNCHANGED txnReq

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
(* Conflict serializability.  This is entirely the `SnapshotIsolation` notion -- the multi-version *)
(* serialization graph over the shared event history -- so it is taken from the instance.          *)
(*                                                                                                *)
(**************************************************************************************************)

SerializableViaPath == SI!SerializableViaPath

----------------------------------------------------------------------------------------------------

TypeOK ==
    /\ clock \in Nat
    /\ DOMAIN dataStore = Keys
    /\ \A c \in CIds : dataStore[AccountKey(c)] = c
    /\ \A c \in CIds : dataStore[SavingsKey(c)] = Tag
    /\ \A c \in CIds : dataStore[CheckingKey(c)] = Tag
    /\ runningTxns \subseteq [id : TxnIds, startTime : Nat, commitTime : Nat \cup {Empty}]
    /\ txnReq \in [TxnIds -> Requests \cup {Empty}]
    /\ DOMAIN txnProg = TxnIds
    /\ \A t \in TxnIds : txnProg[t] = Empty \/ IsBody(txnProg[t])

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
