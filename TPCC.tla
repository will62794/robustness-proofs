--------------------------------- MODULE TPCC ---------------------------------
(**************************************************************************************************)
(*                                                                                                *)
(* A TLA+ model of a (simplified but structurally faithful) TPC-C workload running on top of a    *)
(* key-value store that provides SNAPSHOT ISOLATION.                                              *)
(*                                                                                                *)
(* The snapshot isolation layer is not modelled here.  It is provided by instantiating the        *)
(* `SnapshotIsolation` module, which owns the store state -- the committed data store, the         *)
(* per-transaction snapshots, the clock, the set of running transactions, and the linear event     *)
(* history -- together with the begin / commit / abort actions, read-your-own-writes, and the      *)
(* First-Committer-Wins rule.  This module supplies only the *workload*: it constrains which       *)
(* items each transaction reads and writes, so that the transactions are TPC-C transactions        *)
(* rather than arbitrary ones.                                                                    *)
(*                                                                                                *)
(* The two layers are coupled through the transaction body.  `SnapshotIsolation.StartAndRun`       *)
(* takes a body (a read key set and a write set) as a parameter; this module computes that body    *)
(* from a TPC-C request and the current committed store via `ProgramFor`, then hands it to the     *)
(* instantiated action.                                                                           *)
(*                                                                                                *)
(* THE QUESTION                                                                                   *)
(*                                                                                                *)
(*     Is every history produced by running TPC-C transactions under snapshot isolation           *)
(*     conflict serializable?  (invariant `SerializableViaPath`)                                  *)
(*                                                                                                *)
(* The expected answer is "yes", for a store that detects conflicts per *column group*.  This     *)
(* spec is a machine-checkable version of that claim for a bounded instance; `ColumnGranularity`  *)
(* selects column vs row granularity, and the claim genuinely fails at row granularity.           *)
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
(* The only thing carried beyond the key sets is the value of each write, because a few columns   *)
(* steer control flow (`D_NEXT_O_ID` picks an order id, the `NEW-ORDER` row's existence picks an  *)
(* order to deliver, `ORDER.hdr` picks a customer, `ORDERLINE.items` picks stock rows to scan).   *)
(*                                                                                                *)
(**************************************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences, Functions

(**************************************************************************************************)
(* Scale factors.  Everything about the modelled database is derived from these.                  *)
(**************************************************************************************************)

CONSTANT NumWarehouses      \* warehouses
CONSTANT NumDistricts       \* districts per warehouse
CONSTANT NumCustomers       \* customers per district
CONSTANT NumItems           \* items in the ITEM table
CONSTANT MaxOrders          \* largest order id that may ever exist (bounds the state space)
CONSTANT InitOrders         \* orders 1..InitOrders exist at time 0, all still undelivered
CONSTANT StockLevelDepth    \* Stock-Level examines the last this-many orders
CONSTANT NumTxns            \* how many transactions may run in a behaviour

\* TRUE  -> conflicts are detected per column group (the Fekete et al. setting).
\* FALSE -> conflicts are detected per row (what a typical SI storage engine does).
CONSTANT ColumnGranularity

\* Which of the five TPC-C transaction profiles are allowed to run.
CONSTANT EnabledTxnTypes

\* The item sets a New-Order transaction may order.
CONSTANT NewOrderItemSets

\* The "does not exist" / NULL value.
CONSTANT Empty

WIds == 1..NumWarehouses
DIds == 1..NumDistricts
CIds == 1..NumCustomers
IIds == 1..NumItems
OIds == 1..MaxOrders
TxnIds == 1..NumTxns

AllTxnTypes == {"NewOrder", "Payment", "OrderStatus", "Delivery", "StockLevel"}

ASSUME EnabledTxnTypes \subseteq AllTxnTypes
ASSUME InitOrders \in 0..MaxOrders
ASSUME NewOrderItemSets \subseteq (SUBSET IIds \ {{}})
ASSUME ColumnGranularity \in BOOLEAN

(**************************************************************************************************)
(*                                                                                                *)
(* The schema                                                                                     *)
(*                                                                                                *)
(* A "row key" identifies a TPC-C row.  A "column" names a group of attributes of that row that   *)
(* are always touched together by TPC-C.  The unit of conflict -- the key -- is a row key under   *)
(* row granularity, and a (row key, column) pair under column granularity.                         *)
(*                                                                                                *)
(* The column groups are chosen so that two groups are distinct exactly when some TPC-C statement *)
(* touches one without the other:                                                                 *)
(*                                                                                                *)
(*   WAREHOUSE  tax       W_TAX              read by New-Order                                    *)
(*              ytd       W_YTD              read+written by Payment                              *)
(*   DISTRICT   tax       D_TAX              read by New-Order                                    *)
(*              nextoid   D_NEXT_O_ID        read+written by New-Order, read by Stock-Level       *)
(*              ytd       D_YTD              read+written by Payment                              *)
(*   CUSTOMER   info      C_DISCOUNT,C_LAST  read by New-Order and Order-Status                   *)
(*              balance   C_BALANCE          rw by Payment and Delivery, read by Order-Status     *)
(*   ITEM       info      I_PRICE,I_NAME     read-only for the whole benchmark                    *)
(*   STOCK      qty       S_QUANTITY,S_YTD   rw by New-Order, read by Stock-Level                 *)
(*   ORDER      hdr       O_C_ID,O_ENTRY_D   inserted by New-Order, read by Order-Status/Delivery *)
(*              carrier   O_CARRIER_ID       written by Delivery, read by Order-Status            *)
(*   NEWORDER   row       the whole row      inserted by New-Order, deleted by Delivery           *)
(*   ORDERLINE  items     OL_I_ID,OL_AMOUNT  inserted by New-Order, read by Stock-Level           *)
(*              delivery  OL_DELIVERY_D      written by Delivery, read by Order-Status            *)
(*   HIST       row       the whole row      inserted by Payment, never read                      *)
(*                                                                                                *)
(**************************************************************************************************)

WhKey(w)          == [tbl |-> "WH",        w |-> w]
DistKey(w,d)      == [tbl |-> "DIST",      w |-> w, d |-> d]
CustKey(w,d,c)    == [tbl |-> "CUST",      w |-> w, d |-> d, c |-> c]
ItemKey(i)        == [tbl |-> "ITEM",      i |-> i]
StockKey(w,i)     == [tbl |-> "STOCK",     w |-> w, i |-> i]
OrderKey(w,d,o)   == [tbl |-> "ORDER",     w |-> w, d |-> d, o |-> o]
NewOrdKey(w,d,o)  == [tbl |-> "NEWORDER",  w |-> w, d |-> d, o |-> o]
OrdLineKey(w,d,o) == [tbl |-> "ORDERLINE", w |-> w, d |-> d, o |-> o]
HistKey(t)        == [tbl |-> "HIST",      t |-> t]

RowKeys ==
    {WhKey(w)          : w \in WIds} \cup
    {DistKey(e[1],e[2])          : e \in WIds \X DIds} \cup
    {CustKey(e[1],e[2],e[3])     : e \in WIds \X DIds \X CIds} \cup
    {ItemKey(i)        : i \in IIds} \cup
    {StockKey(e[1],e[2])         : e \in WIds \X IIds} \cup
    {OrderKey(e[1],e[2],e[3])    : e \in WIds \X DIds \X OIds} \cup
    {NewOrdKey(e[1],e[2],e[3])   : e \in WIds \X DIds \X OIds} \cup
    {OrdLineKey(e[1],e[2],e[3])  : e \in WIds \X DIds \X OIds} \cup
    {HistKey(t)        : t \in TxnIds}

ColsOf(tbl) ==
    CASE tbl = "WH"        -> {"tax", "ytd"}
      [] tbl = "DIST"      -> {"tax", "nextoid", "ytd"}
      [] tbl = "CUST"      -> {"info", "balance"}
      [] tbl = "ITEM"      -> {"info"}
      [] tbl = "STOCK"     -> {"qty"}
      [] tbl = "ORDER"     -> {"hdr", "carrier"}
      [] tbl = "NEWORDER"  -> {"row"}
      [] tbl = "ORDERLINE" -> {"items", "delivery"}
      [] tbl = "HIST"      -> {"row"}

\* The column whose presence defines whether the row exists.
PrimaryCol(tbl) ==
    CASE tbl = "ORDER"     -> "hdr"
      [] tbl = "ORDERLINE" -> "items"
      [] tbl = "NEWORDER"  -> "row"
      [] tbl = "HIST"      -> "row"
      [] OTHER             -> CHOOSE c \in ColsOf(tbl) : TRUE

\* The unit of conflict.
Item(base, col) ==
    IF ColumnGranularity
    THEN [x \in (DOMAIN base) \cup {"col"} |-> IF x = "col" THEN col ELSE base[x]]
    ELSE base

Keys == IF ColumnGranularity
        THEN UNION {{Item(b, c) : c \in ColsOf(b.tbl)} : b \in RowKeys}
        ELSE RowKeys

(**************************************************************************************************)
(* Stored values.                                                                                 *)
(*                                                                                                *)
(* Conflict serializability is a property of the *access pattern*, not of the data.  So we only   *)
(* keep the column data that steers control flow (see the header).  Every other column is written *)
(* by exactly the transactions TPC-C says write it, but the value written is the constant tag.    *)
(**************************************************************************************************)

Tag == "v"

\* The value of one column, in either granularity mode.  `Empty` if the row does not exist.
ColVal(snap, base, col) ==
    IF ColumnGranularity
    THEN snap[Item(base, col)]
    ELSE IF snap[base] = Empty THEN Empty ELSE snap[base][col]

RowExists(snap, base) == ColVal(snap, base, PrimaryCol(base.tbl)) # Empty

\* The set of values a column may hold.  This is the value universe handed to `SnapshotIsolation`.
Vals == {Tag, Empty} \cup Nat \cup (SUBSET IIds)

(**************************************************************************************************)
(* Variables.                                                                                     *)
(*                                                                                                *)
(* The store variables -- clock, runningTxns, txnHistory, dataStore, txnSnapshots, txnProg -- are *)
(* declared here and shared with the `SnapshotIsolation` instance below by the default same-name   *)
(* substitution.  `txnReq` is this module's own bookkeeping: the TPC-C request each transaction    *)
(* is executing.                                                                                  *)
(**************************************************************************************************)

VARIABLE clock          \* ticks on every begin and commit
VARIABLE runningTxns    \* set of in-flight transactions
VARIABLE txnHistory     \* the linear event history, the thing we check serializability of
VARIABLE dataStore      \* the committed key-value store
VARIABLE txnSnapshots   \* per-transaction snapshot of the store
VARIABLE txnProg        \* txnId -> the body this request expands to (reads / writes)
VARIABLE txnReq         \* txnId -> the TPC-C request this transaction is executing

vars == <<clock, runningTxns, txnSnapshots, dataStore, txnHistory, txnReq, txnProg>>

(**************************************************************************************************)
(*                                                                                                *)
(* The backing store: an instantiation of the `SnapshotIsolation` module.                          *)
(*                                                                                                *)
(* This provides the begin / commit / abort actions, the First-Committer-Wins rule, and the        *)
(* multi-version serialization graph used to decide conflict serializability.  Its constants are   *)
(* bound to this module's TPC-C schema; its variables are the store variables declared above.      *)
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
(* `SnapshotIsolation` expects (its `BodyType`); values are kept only because a few columns steer *)
(* control flow, the serialization graph itself uses only the keys.                                *)
(*                                                                                                *)
(**************************************************************************************************)

(**************************************************************************************************)
(* Generic helpers.                                                                               *)
(**************************************************************************************************)

Min(S) == CHOOSE x \in S : \A y \in S : x =< y
Max(S) == CHOOSE x \in S : \A y \in S : y =< x

(**************************************************************************************************)
(*                                                                                                *)
(* Statements                                                                                     *)
(*                                                                                                *)
(* A TPC-C statement touches a set of columns of one row.  Under column granularity it touches   *)
(* one key per column; under row granularity it collapses to the single row key.  A row-          *)
(* granularity write must merge, so that e.g. Payment updating D_YTD does not clobber the         *)
(* D_NEXT_O_ID stored in the same row value.                                                      *)
(*                                                                                                *)
(**************************************************************************************************)

\* The set of keys read by reading columns `cols` of row `base`.
RdKeys(base, cols) ==
    IF ColumnGranularity THEN {Item(base, c) : c \in cols} ELSE {base}

\* The set of write operations that update row `base`, setting the columns in DOMAIN upd.
WrOps(snap, base, upd) ==
    IF ColumnGranularity
    THEN {[type |-> "write", key |-> Item(base, c), val |-> upd[c]] : c \in DOMAIN upd}
    ELSE {[type |-> "write", key |-> base,
           val |-> [c \in ColsOf(base.tbl) |-> IF c \in DOMAIN upd THEN upd[c] ELSE snap[base][c]]]}

\* The set of write operations that delete row `base`.
DelOps(base) ==
    IF ColumnGranularity
    THEN {[type |-> "write", key |-> Item(base, c), val |-> Empty] : c \in ColsOf(base.tbl)}
    ELSE {[type |-> "write", key |-> base, val |-> Empty]}

(**************************************************************************************************)
(*                                                                                                *)
(* The TPC-C transaction profiles                                                                 *)
(*                                                                                                *)
(* Each profile maps (request parameters, begin snapshot) to a body.                               *)
(*                                                                                                *)
(* PREDICATE READS AND PHANTOMS                                                                   *)
(*                                                                                                *)
(* Three transactions do not address rows by primary key; they evaluate a predicate (Delivery:    *)
(* "lowest undelivered order"; Order-Status: "highest order of this customer"; Stock-Level: "the  *)
(* order lines of the last StockLevelDepth orders").  If such a transaction only recorded reads    *)
(* of the rows that *matched*, the model would miss phantom anti-dependencies.  So predicate      *)
(* evaluation is modelled as a range scan: the transaction reads every key in the scanned range,   *)
(* present or absent.                                                                             *)
(*                                                                                                *)
(**************************************************************************************************)

(*----------------------------------------------------------------------------------------------*)
(* NEW-ORDER                                                                                     *)
(*----------------------------------------------------------------------------------------------*)
NewOrderProgram(req, snap) ==
    LET w == req.w   d == req.d   c == req.c   sw == req.sw   items == req.items
        o == ColVal(snap, DistKey(w,d), "nextoid")
    IN  [ reads |-> RdKeys(WhKey(w), {"tax"})
                 \cup RdKeys(DistKey(w,d), {"tax", "nextoid"})
                 \cup RdKeys(CustKey(w,d,c), {"info"})
                 \cup (UNION {RdKeys(ItemKey(i), {"info"}) : i \in items})
                 \cup (UNION {RdKeys(StockKey(sw,i), {"qty"}) : i \in items}),
          writes |-> WrOps(snap, DistKey(w,d), [nextoid |-> o + 1])
                 \cup (UNION {WrOps(snap, StockKey(sw,i), [qty |-> Tag]) : i \in items})
                 \cup WrOps(snap, OrderKey(w,d,o),   [hdr |-> c, carrier |-> Tag])
                 \cup WrOps(snap, NewOrdKey(w,d,o),  [row |-> Tag])
                 \cup WrOps(snap, OrdLineKey(w,d,o), [items |-> items, delivery |-> Tag]) ]

NewOrderEnabled(req, snap) == ColVal(snap, DistKey(req.w, req.d), "nextoid") \in OIds

(*----------------------------------------------------------------------------------------------*)
(* PAYMENT                                                                                       *)
(*----------------------------------------------------------------------------------------------*)
PaymentProgram(tid, req, snap) ==
    LET w == req.w   d == req.d   cw == req.cw   cd == req.cd   c == req.c IN
    [ reads  |-> RdKeys(WhKey(w), {"ytd"})
              \cup RdKeys(DistKey(w,d), {"ytd"})
              \cup RdKeys(CustKey(cw,cd,c), {"balance"}),
      writes |-> WrOps(snap, WhKey(w), [ytd |-> Tag])
              \cup WrOps(snap, DistKey(w,d), [ytd |-> Tag])
              \cup WrOps(snap, CustKey(cw,cd,c), [balance |-> Tag])
              \cup WrOps(snap, HistKey(tid), [row |-> Tag]) ]

(*----------------------------------------------------------------------------------------------*)
(* DELIVERY                                                                                      *)
(*----------------------------------------------------------------------------------------------*)
DeliveryForDistrict(w, d, snap) ==
    LET undelivered == {o \in OIds : RowExists(snap, NewOrdKey(w,d,o))}
    IN IF undelivered = {}
       THEN [reads |-> {}, writes |-> {}]
       ELSE LET o    == Min(undelivered)
                cust == ColVal(snap, OrderKey(w,d,o), "hdr")
            IN [ reads  |-> RdKeys(NewOrdKey(w,d,o), {"row"})
                         \cup RdKeys(OrderKey(w,d,o), {"hdr"})
                         \cup RdKeys(OrdLineKey(w,d,o), {"items"})
                         \cup RdKeys(CustKey(w,d,cust), {"balance"}),
                 writes |-> DelOps(NewOrdKey(w,d,o))
                         \cup WrOps(snap, OrderKey(w,d,o), [carrier |-> Tag])
                         \cup WrOps(snap, OrdLineKey(w,d,o), [delivery |-> Tag])
                         \cup WrOps(snap, CustKey(w,d,cust), [balance |-> Tag]) ]

DeliveryProgram(req, snap) ==
    LET R == UNION {DeliveryForDistrict(req.w, d, snap).reads  : d \in DIds}
        W == UNION {DeliveryForDistrict(req.w, d, snap).writes : d \in DIds}
    IN [reads |-> R, writes |-> W]

(*----------------------------------------------------------------------------------------------*)
(* ORDER-STATUS  (read only)                                                                     *)
(*----------------------------------------------------------------------------------------------*)
OrderStatusProgram(req, snap) ==
    LET w == req.w   d == req.d   c == req.c
        mine == {o \in OIds : /\ RowExists(snap, OrderKey(w,d,o))
                              /\ ColVal(snap, OrderKey(w,d,o), "hdr") = c}
    IN [ reads  |-> RdKeys(CustKey(w,d,c), {"info", "balance"})
                 \cup (UNION {RdKeys(OrderKey(w,d,o), {"hdr", "carrier"}) : o \in OIds})
                 \cup (IF mine = {} THEN {} ELSE RdKeys(OrdLineKey(w,d,Max(mine)), {"items", "delivery"})),
         writes |-> {} ]

(*----------------------------------------------------------------------------------------------*)
(* STOCK-LEVEL  (read only)                                                                      *)
(*----------------------------------------------------------------------------------------------*)
StockLevelProgram(req, snap) ==
    LET w == req.w   d == req.d
        nextO   == ColVal(snap, DistKey(w,d), "nextoid")
        recent  == {o \in OIds : o < nextO /\ nextO - o =< StockLevelDepth}
        present == {o \in recent : RowExists(snap, OrdLineKey(w,d,o))}
        items   == UNION {ColVal(snap, OrdLineKey(w,d,o), "items") : o \in present}
    IN [ reads  |-> RdKeys(DistKey(w,d), {"nextoid"})
                 \cup (UNION {RdKeys(OrdLineKey(w,d,o), {"items"}) : o \in recent})
                 \cup (UNION {RdKeys(StockKey(w,i), {"qty"}) : i \in items}),
         writes |-> {} ]

(**************************************************************************************************)
(* The set of TPC-C requests a client may submit.                                                 *)
(**************************************************************************************************)

Requests ==
    (IF "NewOrder" \in EnabledTxnTypes
       THEN [type : {"NewOrder"}, w : WIds, d : DIds, c : CIds, sw : WIds, items : NewOrderItemSets]
       ELSE {}) \cup
    (IF "Payment" \in EnabledTxnTypes
       THEN [type : {"Payment"}, w : WIds, d : DIds, cw : WIds, cd : DIds, c : CIds]
       ELSE {}) \cup
    (IF "OrderStatus" \in EnabledTxnTypes
       THEN [type : {"OrderStatus"}, w : WIds, d : DIds, c : CIds]
       ELSE {}) \cup
    (IF "Delivery" \in EnabledTxnTypes
       THEN [type : {"Delivery"}, w : WIds]
       ELSE {}) \cup
    (IF "StockLevel" \in EnabledTxnTypes
       THEN [type : {"StockLevel"}, w : WIds, d : DIds]
       ELSE {})

\* A request may be blocked purely by the model's bounds.
DeliveryEnabled(req, snap) ==
    \E d \in DIds : \E o \in OIds : RowExists(snap, NewOrdKey(req.w, d, o))

ReqEnabled(req, snap) ==
    IF req.type = "NewOrder" THEN NewOrderEnabled(req, snap)
    ELSE IF req.type = "Delivery" THEN DeliveryEnabled(req, snap)
    ELSE TRUE

ProgramFor(tid, req, snap) ==
    CASE req.type = "NewOrder"    -> NewOrderProgram(req, snap)
      [] req.type = "Payment"     -> PaymentProgram(tid, req, snap)
      [] req.type = "OrderStatus" -> OrderStatusProgram(req, snap)
      [] req.type = "Delivery"    -> DeliveryProgram(req, snap)
      [] req.type = "StockLevel"  -> StockLevelProgram(req, snap)

----------------------------------------------------------------------------------------------------

(**************************************************************************************************)
(* Initial state                                                                                  *)
(*                                                                                                *)
(* The store's initial value is workload-specific (a populated TPC-C database), so this module     *)
(* supplies it rather than reusing `SnapshotIsolation`'s all-empty `Init`.                          *)
(**************************************************************************************************)

InitOrderCust(o) == ((o - 1) % NumCustomers) + 1
InitOrderItems   == IIds

InitRow(k) ==
    CASE k.tbl = "WH"        -> [tax |-> Tag, ytd |-> Tag]
      [] k.tbl = "DIST"      -> [tax |-> Tag, ytd |-> Tag, nextoid |-> InitOrders + 1]
      [] k.tbl = "CUST"      -> [info |-> Tag, balance |-> Tag]
      [] k.tbl = "ITEM"      -> [info |-> Tag]
      [] k.tbl = "STOCK"     -> [qty |-> Tag]
      [] k.tbl = "ORDER"     -> IF k.o =< InitOrders
                                    THEN [hdr |-> InitOrderCust(k.o), carrier |-> Tag] ELSE Empty
      [] k.tbl = "NEWORDER"  -> IF k.o =< InitOrders THEN [row |-> Tag] ELSE Empty
      [] k.tbl = "ORDERLINE" -> IF k.o =< InitOrders
                                    THEN [items |-> InitOrderItems, delivery |-> Tag] ELSE Empty
      [] k.tbl = "HIST"      -> Empty

InitStore ==
    IF ColumnGranularity
    THEN [k \in Keys |-> LET base == [f \in (DOMAIN k) \ {"col"} |-> k[f]] IN
                         IF InitRow(base) = Empty THEN Empty ELSE InitRow(base)[k.col]]
    ELSE [k \in Keys |-> InitRow(k)]

Init ==
    /\ clock        = 0
    /\ runningTxns  = {}
    /\ txnHistory   = <<>>
    /\ dataStore    = InitStore
    /\ txnSnapshots = [t \in TxnIds |-> Empty]
    /\ txnProg      = [t \in TxnIds |-> Empty]
    /\ txnReq       = [t \in TxnIds |-> Empty]

----------------------------------------------------------------------------------------------------

(**************************************************************************************************)
(*                                                                                                *)
(* Actions                                                                                        *)
(*                                                                                                *)
(* These are thin wrappers over `SnapshotIsolation`.  `StartAndRun` picks a TPC-C request, turns   *)
(* it into a body via `ProgramFor`, and hands that body to `SI!StartAndRun`; commit and abort      *)
(* delegate entirely.  The only state this module adds is `txnReq`, which each action must pin.    *)
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

TypeOK ==
    /\ clock \in Nat
    /\ DOMAIN dataStore = Keys
    /\ runningTxns \subseteq [id : TxnIds, startTime : Nat, commitTime : Nat \cup {Empty}]
    /\ txnReq \in [TxnIds -> Requests \cup {Empty}]

(**************************************************************************************************)
(* COVERAGE CHECKS.  These are meant to FAIL; a passing run means the model is too small.         *)
(**************************************************************************************************)
Cov_AllTxnsCommit  == Cardinality(SI!CommittedTxns(txnHistory)) < NumTxns
Cov_SomeTxnAborts  == SI!AbortedTxns(txnHistory) = {}
Cov_ConcurrentTxns == Cardinality(runningTxns) < 2
Cov_RWEdgeExists ==
    ~\E t1, t2 \in SI!CommittedTxns(txnHistory) :
        t1 # t2 /\ SI!RWDependency(txnHistory, t1, t2)

====================================================================================================
