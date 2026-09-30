--------------------------------- MODULE TPCC ---------------------------------
(**************************************************************************************************)
(*                                                                                                *)
(* A TLA+ model of a (simplified but structurally faithful) TPC-C workload running on top of a    *)
(* key-value store that provides SNAPSHOT ISOLATION.                                              *)
(*                                                                                                *)
(* The snapshot isolation layer is NOT re-implemented here.  It is the unmodified                 *)
(* `SnapshotIsolation` module from https://github.com/will62794/snapshot-isolation-spec, which we *)
(* instantiate below.  All of the subtle parts of SI -- the begin snapshot, read-your-own-writes, *)
(* the First-Committer-Wins write-conflict rule, and the multi-version serialization graph (MVSG) *)
(* used to decide conflict serializability -- come from that module verbatim.  This module only   *)
(* adds a *workload*: it constrains which items each transaction reads and writes, and in what    *)
(* order, so that the transactions are TPC-C transactions rather than arbitrary ones.             *)
(*                                                                                                *)
(* THE QUESTION                                                                                   *)
(*                                                                                                *)
(*     Is every history produced by running TPC-C transactions under snapshot isolation           *)
(*     conflict serializable?  (invariant `Serializable`)                                         *)
(*                                                                                                *)
(* The expected answer is "yes", and the reason is due to Fekete, Liarokapis, O'Neil, O'Neil and  *)
(* Shasha, "Making Snapshot Isolation Serializable" (TODS 2005), Section 5, which analyzes        *)
(* exactly this: the static dependency graph of the TPC-C transaction mix contains no "dangerous  *)
(* structure" (no two consecutive read-write anti-dependency edges on a cycle), and therefore     *)
(* every SI execution of TPC-C is serializable.  This spec is a machine-checkable version of that *)
(* argument for a bounded instance.                                                               *)
(*                                                                                                *)
(* CONFLICT GRANULARITY IS PART OF THE THEOREM, NOT A DETAIL                                      *)
(*                                                                                                *)
(* That result holds at *attribute* granularity, and it genuinely fails at row granularity.  The  *)
(* `ColumnGranularity` constant selects which one is modelled, because the difference is the most *)
(* interesting thing this spec has to say.  Two examples, both of which TLC finds:                *)
(*                                                                                                *)
(*   * New-Order reads W_TAX; Payment writes W_YTD.  Same WAREHOUSE row, different columns.       *)
(*   * Stock-Level reads D_NEXT_O_ID; Payment writes D_YTD.  Same DISTRICT row.                   *)
(*                                                                                                *)
(* At row granularity each pair is a dependency edge, and those spurious edges are enough to      *)
(* close a cycle -- so a store that does SI conflict detection per row (which is what most real   *)
(* engines do) does NOT give you serializable TPC-C for free.  Set `ColumnGranularity = FALSE` to *)
(* see a counterexample in a handful of seconds.                                                  *)
(*                                                                                                *)
(**************************************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences

(**************************************************************************************************)
(* Scale factors.  Everything about the modelled database is derived from these.  Keep them tiny; *)
(* the interesting concurrency structure of TPC-C shows up at 1 warehouse / 1-2 districts.        *)
(**************************************************************************************************)

CONSTANT NumWarehouses      \* warehouses
CONSTANT NumDistricts       \* districts per warehouse
CONSTANT NumCustomers       \* customers per district
CONSTANT NumItems           \* items in the ITEM table
CONSTANT MaxOrders          \* largest order id that may ever exist (bounds the state space)
CONSTANT InitOrders         \* orders 1..InitOrders exist at time 0, all still undelivered
CONSTANT StockLevelDepth    \* Stock-Level examines the last this-many orders (TPC-C says 20)
CONSTANT NumTxns            \* how many transactions may run in a behaviour

\* TRUE  -> conflicts are detected per column group (the Fekete et al. setting).
\* FALSE -> conflicts are detected per row (what a typical SI storage engine does).
CONSTANT ColumnGranularity

\* Which of the five TPC-C transaction profiles are allowed to run.  Subset of
\* {"NewOrder", "Payment", "OrderStatus", "Delivery", "StockLevel"}.
CONSTANT EnabledTxnTypes

\* The item sets a New-Order transaction may order.  TPC-C uses 5..15 line items; a model with
\* one or two is enough to expose the New-Order/Stock-Level and New-Order/New-Order structure.
\* Must be a set of non-empty subsets of IIds.
CONSTANT NewOrderItemSets

\* The "does not exist" / NULL value.  Also the `Empty` of the snapshot isolation module.
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
(* Generic helpers.                                                                               *)
(*                                                                                                *)
(* `Merge` is the TLC module's infix `@@` operator, written out here.  We do not EXTEND TLC,      *)
(* so that the spec depends only on modules whose operators TLAPS can reason about: the TLC      *)
(* module's operators are implemented (or overridden) by the TLC Java runtime and have no         *)
(* useful interpretation in a proof.  This is the only thing the spec used TLC for.               *)
(**************************************************************************************************)

\* Merge two functions, with the second taking precedence on their shared domain.
Merge(f, g) ==
    [x \in (DOMAIN f) \cup (DOMAIN g) |-> IF x \in DOMAIN g THEN g[x] ELSE f[x]]

----------------------------------------------------------------------------------------------------

(**************************************************************************************************)
(*                                                                                                *)
(* The schema                                                                                     *)
(*                                                                                                *)
(* A "row key" identifies a TPC-C row.  A "column" names a group of attributes of that row that   *)
(* are always touched together by TPC-C.  The unit of conflict -- the key handed to the snapshot  *)
(* isolation module -- is a row key under row granularity, and a (row key, column) pair under     *)
(* column granularity.                                                                            *)
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
(* Two deliberate aggregations, both of which preserve the dependency graph exactly:              *)
(*                                                                                                *)
(*   * ORDERLINE(w,d,o) stands for *all* line items of order o.  Every TPC-C statement that       *)
(*     touches order lines touches all lines of an order together, so splitting them per-line     *)
(*     would add no edges to the MVSG.                                                            *)
(*                                                                                                *)
(*   * HIST(t) is the HISTORY row inserted by Payment transaction t.  HISTORY is insert-only with *)
(*     a fresh row per transaction, so a per-transaction key is exact: it can never conflict.     *)
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

\* The column whose presence defines whether the row exists.  For every insert-then-delete table
\* the insert writes all columns and the delete clears all columns, so any choice agrees.
PrimaryCol(tbl) ==
    CASE tbl = "ORDER"     -> "hdr"
      [] tbl = "ORDERLINE" -> "items"
      [] tbl = "NEWORDER"  -> "row"
      [] tbl = "HIST"      -> "row"
      [] OTHER             -> CHOOSE c \in ColsOf(tbl) : TRUE

\* A fixed total order on column names, so that a statement touching several columns expands to a
\* deterministic sequence of operations rather than an unordered set.
ColOrder == <<"tax", "ytd", "nextoid", "info", "balance", "qty", "hdr", "carrier",
              "items", "delivery", "row">>
SeqOfCols(S) == SelectSeq(ColOrder, LAMBDA c : c \in S)

\* The unit of conflict.
Item(base, col) == IF ColumnGranularity THEN Merge(base, [col |-> col]) ELSE base

Keys == IF ColumnGranularity
        THEN UNION {{Item(b, c) : c \in ColsOf(b.tbl)} : b \in RowKeys}
        ELSE RowKeys

(**************************************************************************************************)
(* Stored values.                                                                                 *)
(*                                                                                                *)
(* Conflict serializability is a property of the *access pattern* -- which transaction read or    *)
(* wrote which item, and when -- not of the data.  So we only keep the column data that steers    *)
(* control flow, i.e.  that decides *which items get touched*:                                    *)
(*                                                                                                *)
(*   * DIST.nextoid    -- picks the order id a New-Order inserts, and the range Stock-Level scans *)
(*   * NEWORDER.row    -- its existence picks the order a Delivery delivers                       *)
(*   * ORDER.hdr       -- the customer id, picks the order an Order-Status reports on             *)
(*   * ORDERLINE.items -- picks the STOCK rows a Stock-Level reads                                *)
(*                                                                                                *)
(* Every other column is written by exactly the transactions TPC-C says write it, but the value   *)
(* written is the constant tag "v".  Dropping those payloads does not change a single edge of the *)
(* MVSG, and it keeps the reachable state space small.                                            *)
(**************************************************************************************************)

Tag == "v"

\* The value of one column, in either granularity mode.  `Empty` if the row does not exist.
ColVal(snap, base, col) ==
    IF ColumnGranularity
    THEN snap[Item(base, col)]
    ELSE IF snap[base] = Empty THEN Empty ELSE snap[base][col]

RowExists(snap, base) == ColVal(snap, base, PrimaryCol(base.tbl)) # Empty

----------------------------------------------------------------------------------------------------

(**************************************************************************************************)
(* Variables.  The first five are the variables of the snapshot isolation module (they are bound  *)
(* by name when we INSTANCE it).  The last three are bookkeeping for the workload layer.          *)
(**************************************************************************************************)

VARIABLE clock          \* SI: ticks on every begin and commit
VARIABLE runningTxns    \* SI: set of in-flight transactions
VARIABLE txnHistory     \* SI: the linear event history, the thing we check serializability of
VARIABLE dataStore      \* SI: the committed key-value store
VARIABLE txnSnapshots   \* SI: per-transaction snapshot of the store

VARIABLE txnReq         \* txnId -> the TPC-C request this transaction is executing
VARIABLE txnProg        \* txnId -> the sequence of read/write ops that request expands to

siVars == <<clock, runningTxns, txnSnapshots, dataStore, txnHistory>>
wlVars == <<txnReq, txnProg>>
vars   == <<clock, runningTxns, txnSnapshots, dataStore, txnHistory, txnReq, txnProg>>

(**************************************************************************************************)
(* Instantiate the snapshot isolation specification.  From here on, `SI!Foo` is Foo as defined in *)
(* SnapshotIsolation.tla, operating on the variables declared above.                              *)
(**************************************************************************************************)

SI == INSTANCE SnapshotIsolation WITH
    txnIds <- TxnIds,
    keys   <- Keys,
    values <- {Tag},   \* only used by that module's (unchecked) type invariant
    Empty  <- Empty

----------------------------------------------------------------------------------------------------

(**************************************************************************************************)
(* Sequence helpers.                                                                              *)
(**************************************************************************************************)

Min(S) == CHOOSE x \in S : \A y \in S : x =< y
Max(S) == CHOOSE x \in S : \A y \in S : y =< x

\* A finite set of naturals as an ascending sequence.  Written without recursion (TLAPS
\* does not support recursive operator definitions) as the unique injective, increasing
\* enumeration of S.
SeqOf(S) ==
    CHOOSE s \in [1..Cardinality(S) -> S] :
        /\ \A i, j \in DOMAIN s : s[i] = s[j] => i = j
        /\ \A i \in 1..(Len(s) - 1) : s[i] < s[i+1]

\* Concatenation of a sequence of sequences, without recursion.  The result has length equal
\* to the sum of the block lengths, and block i occupies positions OffLens(s,i)+1 .. +Len(s[i]).
SumLens(s) == Cardinality(UNION {{i} \X (1..Len(s[i])) : i \in DOMAIN s})
OffLens(s, i) == Cardinality(UNION {{j} \X (1..Len(s[j])) : j \in {j \in DOMAIN s : j < i}})

\* Position k of the result comes from block Blk(s,k), at offset k - OffLens(s, Blk(s,k)).
\* (Retained only for the older CHOOSE-based development; `Flatten` below no longer uses them.)
Blk(s, k) == CHOOSE i \in DOMAIN s :
                 /\ OffLens(s, i) < k
                 /\ k =< OffLens(s, i) + Len(s[i])

\* Concatenation of the blocks, as a recursive *function* (TLAPS rejects recursive operators,
\* but accepts recursive functions, and this form has an easy range lemma -- unlike the CHOOSE-
\* based `Blk` version, whose range characterization needs OffLens/SumLens partition arithmetic).
Flatten(s) == LET f[i \in 0..Len(s)] == IF i = 0 THEN <<>> ELSE f[i-1] \o s[i]
              IN f[Len(s)]

\* Apply `f` to each element of the ascending sequence of `ids`, concatenating the results.
ConcatOver(f(_), ids) == LET s == SeqOf(ids) IN Flatten([i \in 1..Len(s) |-> f(s[i])])

----------------------------------------------------------------------------------------------------

(**************************************************************************************************)
(*                                                                                                *)
(* Statements                                                                                     *)
(*                                                                                                *)
(* A TPC-C statement touches a set of columns of one row.  Under column granularity it expands to *)
(* one operation per column; under row granularity it collapses to a single operation on the row. *)
(* A row-granularity write must merge, so that e.g.  Payment updating D_YTD does not clobber the  *)
(* D_NEXT_O_ID stored in the same row value.                                                      *)
(**************************************************************************************************)

\* Read columns `cols` of row `base`.
Rd(snap, base, cols) ==
    IF ColumnGranularity
    THEN LET s == SeqOfCols(cols) IN
         [i \in 1..Len(s) |-> [type |-> "read",
                               key  |-> Item(base, s[i]),
                               val  |-> ColVal(snap, base, s[i])]]
    ELSE << [type |-> "read", key |-> base, val |-> snap[base]] >>

\* Update row `base`, setting the columns in DOMAIN upd to upd[c].  For an insert, `upd` must
\* cover every column of the table.
Wr(snap, base, upd) ==
    IF ColumnGranularity
    THEN LET s == SeqOfCols(DOMAIN upd) IN
         [i \in 1..Len(s) |-> [type |-> "write",
                               key  |-> Item(base, s[i]),
                               val  |-> upd[s[i]]]]
    ELSE << [type |-> "write",
             key  |-> base,
             val  |-> [c \in ColsOf(base.tbl) |->
                          IF c \in DOMAIN upd THEN upd[c] ELSE snap[base][c]]] >>

\* Delete row `base`.
Del(base) ==
    IF ColumnGranularity
    THEN LET s == SeqOfCols(ColsOf(base.tbl)) IN
         [i \in 1..Len(s) |-> [type |-> "write", key |-> Item(base, s[i]), val |-> Empty]]
    ELSE << [type |-> "write", key |-> base, val |-> Empty] >>

----------------------------------------------------------------------------------------------------

(**************************************************************************************************)
(*                                                                                                *)
(* The TPC-C transaction profiles                                                                 *)
(*                                                                                                *)
(* Each profile maps (request parameters, begin snapshot) to the sequence of operations the       *)
(* transaction performs.                                                                          *)
(*                                                                                                *)
(* ----------------------------------------------------------------------------------------      *)
(* PREDICATE READS AND PHANTOMS                                                                   *)
(*                                                                                                *)
(* Three TPC-C transactions do not address rows by primary key; they evaluate a predicate:        *)
(*                                                                                                *)
(*   * Delivery     -- "the lowest-numbered undelivered order in this district"                   *)
(*   * Order-Status -- "the highest-numbered order belonging to this customer"                    *)
(*   * Stock-Level  -- "the order lines of the last StockLevelDepth orders"                       *)
(*                                                                                                *)
(* If such a transaction only recorded reads of the rows that *matched*, the model would miss     *)
(* phantom anti-dependencies: a concurrent insert that would have matched is a real read-write    *)
(* conflict, but it leaves no trace in the matching set.  So predicate evaluation is modelled as  *)
(* a *range scan*: the transaction reads every key in the scanned range, present or absent.  That *)
(* is both sound and what a real engine without predicate locking does.                           *)
(*                                                                                                *)
(* One place this is conservative rather than exact: Order-Status's scan covers orders belonging  *)
(* to *other* customers too, because it is modelled as a range scan rather than a probe of the    *)
(* (o_w_id, o_d_id, o_c_id) index.  That can only add rw-edges, never remove them, so a           *)
(* "serializable" verdict remains valid; a violation would need checking against this.            *)
(**************************************************************************************************)

(*----------------------------------------------------------------------------------------------*)
(* NEW-ORDER (45% of the TPC-C mix).                                                             *)
(*                                                                                               *)
(* Reads W_TAX, reads and *increments* D_NEXT_O_ID, reads the customer, reads each item, reads   *)
(* and updates the STOCK row of each item at the supplying warehouse `sw` (remote ~1% of the     *)
(* time in TPC-C), and inserts one ORDER / NEW-ORDER / ORDER-LINE row.                           *)
(*                                                                                               *)
(* The D_NEXT_O_ID update is the backbone of TPC-C's serializability under SI: it makes any two  *)
(* New-Orders on the same district write-conflict, so First-Committer-Wins aborts one of them.   *)
(*----------------------------------------------------------------------------------------------*)
NewOrderProgram(req, snap) ==
    LET w == req.w   d == req.d   c == req.c   sw == req.sw   items == req.items
        o == ColVal(snap, DistKey(w,d), "nextoid")
        RdItem(i)  == Rd(snap, ItemKey(i), {"info"})
        RdStock(i) == Rd(snap, StockKey(sw,i), {"qty"})
        WrStock(i) == Wr(snap, StockKey(sw,i), [qty |-> Tag])
    IN Rd(snap, WhKey(w), {"tax"})
       \o Rd(snap, DistKey(w,d), {"tax", "nextoid"})
       \o Wr(snap, DistKey(w,d), [nextoid |-> o + 1])
       \o Rd(snap, CustKey(w,d,c), {"info"})
       \o ConcatOver(RdItem, items)
       \o ConcatOver(RdStock, items)
       \o ConcatOver(WrStock, items)
       \o Wr(snap, OrderKey(w,d,o),   [hdr |-> c, carrier |-> Tag])
       \o Wr(snap, NewOrdKey(w,d,o),  [row |-> Tag])
       \o Wr(snap, OrdLineKey(w,d,o), [items |-> items, delivery |-> Tag])

\* A New-Order can only run if the order id it would allocate is still inside the modelled range.
NewOrderEnabled(req, snap) == ColVal(snap, DistKey(req.w, req.d), "nextoid") \in OIds

(*----------------------------------------------------------------------------------------------*)
(* PAYMENT (43%).                                                                                *)
(*                                                                                               *)
(* Updates W_YTD on the home warehouse, D_YTD on the home district, C_BALANCE on the customer    *)
(* (who may live in a different warehouse/district -- 15% remote in TPC-C), and inserts a        *)
(* HISTORY row.  Payment also reads W_NAME / D_NAME to build the history record, but no          *)
(* transaction ever writes those, so omitting them removes no edge.                              *)
(*----------------------------------------------------------------------------------------------*)
PaymentProgram(tid, req, snap) ==
    LET w == req.w   d == req.d   cw == req.cw   cd == req.cd   c == req.c IN
       Rd(snap, WhKey(w), {"ytd"})
    \o Wr(snap, WhKey(w), [ytd |-> Tag])
    \o Rd(snap, DistKey(w,d), {"ytd"})
    \o Wr(snap, DistKey(w,d), [ytd |-> Tag])
    \o Rd(snap, CustKey(cw,cd,c), {"balance"})
    \o Wr(snap, CustKey(cw,cd,c), [balance |-> Tag])
    \o Wr(snap, HistKey(tid), [row |-> Tag])

(*----------------------------------------------------------------------------------------------*)
(* DELIVERY (4%).                                                                                *)
(*                                                                                               *)
(* For each district of a warehouse: find the oldest undelivered order (a predicate read over    *)
(* the NEW-ORDER range, modelled as a full scan of that district's NEW-ORDER keys), delete that  *)
(* NEW-ORDER row, stamp O_CARRIER_ID, stamp OL_DELIVERY_D on its order lines, and credit         *)
(* C_BALANCE.  All districts are handled in one transaction, the stronger of the two variants    *)
(* TPC-C permits.                                                                                *)
(*----------------------------------------------------------------------------------------------*)
DeliveryForDistrict(w, d, snap) ==
    LET undelivered == {o \in OIds : RowExists(snap, NewOrdKey(w,d,o))}
    IN IF undelivered = {}
       THEN <<>>   \* index probe on (w,d) finds no undelivered order: no rows touched
       ELSE LET o    == Min(undelivered)
                cust == ColVal(snap, OrderKey(w,d,o), "hdr")
            IN    Rd(snap, NewOrdKey(w,d,o), {"row"})
               \o Del(NewOrdKey(w,d,o))
               \o Rd(snap, OrderKey(w,d,o), {"hdr"})
               \o Wr(snap, OrderKey(w,d,o), [carrier |-> Tag])
               \o Rd(snap, OrdLineKey(w,d,o), {"items"})       \* SUM(ol_amount)
               \o Wr(snap, OrdLineKey(w,d,o), [delivery |-> Tag])
               \o Rd(snap, CustKey(w,d,cust), {"balance"})
               \o Wr(snap, CustKey(w,d,cust), [balance |-> Tag])

\* Concatenate DeliveryForDistrict over the districts of `ds`, without recursion.
DeliveryOverDistricts(w, ds, snap) ==
    Flatten([i \in 1..Len(ds) |-> DeliveryForDistrict(w, ds[i], snap)])

DeliveryProgram(req, snap) == DeliveryOverDistricts(req.w, SeqOf(DIds), snap)

(*----------------------------------------------------------------------------------------------*)
(* ORDER-STATUS (4%).  Read only.                                                                *)
(*                                                                                               *)
(* Reads the customer row, finds that customer's most recent order (predicate read, modelled as  *)
(* a scan of the district's ORDER range), and reads its order lines.                             *)
(*----------------------------------------------------------------------------------------------*)
OrderStatusProgram(req, snap) ==
    LET w == req.w   d == req.d   c == req.c
        RdOrder(o) == Rd(snap, OrderKey(w,d,o), {"hdr", "carrier"})
        scan == ConcatOver(RdOrder, OIds)
        mine == {o \in OIds : /\ RowExists(snap, OrderKey(w,d,o))
                              /\ ColVal(snap, OrderKey(w,d,o), "hdr") = c}
    IN    Rd(snap, CustKey(w,d,c), {"info", "balance"})
       \o scan
       \o (IF mine = {} THEN <<>>
                        ELSE Rd(snap, OrdLineKey(w,d,Max(mine)), {"items", "delivery"}))

(*----------------------------------------------------------------------------------------------*)
(* STOCK-LEVEL (4%).  Read only.                                                                 *)
(*                                                                                               *)
(* Reads D_NEXT_O_ID, reads OL_I_ID from the order lines of the last StockLevelDepth orders of   *)
(* the district, and reads S_QUANTITY of every item so found, counting those below a threshold.  *)
(* The threshold only affects the answer, never which rows are touched, so it is not modelled.   *)
(*                                                                                               *)
(* This is the transaction that read-write conflicts with New-Order on STOCK, and it is the      *)
(* read-only transaction that Fekete et al. show cannot close a dangerous cycle in TPC-C.  Note  *)
(* that it reads only OL_I_ID, so it does NOT conflict with Delivery's OL_DELIVERY_D write -- a  *)
(* distinction that exists only at column granularity.                                           *)
(*----------------------------------------------------------------------------------------------*)
StockLevelProgram(req, snap) ==
    LET w == req.w   d == req.d
        nextO   == ColVal(snap, DistKey(w,d), "nextoid")
        recent  == {o \in OIds : o < nextO /\ nextO - o =< StockLevelDepth}
        present == {o \in recent : RowExists(snap, OrdLineKey(w,d,o))}
        items   == UNION {ColVal(snap, OrdLineKey(w,d,o), "items") : o \in present}
        RdOl(o)    == Rd(snap, OrdLineKey(w,d,o), {"items"})
        RdStock(i) == Rd(snap, StockKey(w,i), {"qty"})
    IN    Rd(snap, DistKey(w,d), {"nextoid"})
       \o ConcatOver(RdOl, recent)
       \o ConcatOver(RdStock, items)

(**************************************************************************************************)
(* The set of TPC-C requests a client may submit, and the expansion of a request to operations.   *)
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

\* A request may be blocked purely by the model's bounds (New-Order running out of order ids, or
\* Delivery finding no undelivered order to deliver -- in which case its program would be empty,
\* and the snapshot isolation module cannot commit or abort a no-op transaction).
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
(*                                                                                                *)
(* Initial state                                                                                  *)
(*                                                                                                *)
(* A freshly loaded TPC-C database, shrunk: every WAREHOUSE, DISTRICT, CUSTOMER, ITEM and STOCK   *)
(* row exists; orders 1..InitOrders exist and are all still undelivered (TPC-C's load leaves the  *)
(* newest third of orders undelivered); D_NEXT_O_ID points one past the last loaded order.        *)
(* Initial orders are dealt round-robin to customers.                                             *)
(**************************************************************************************************)

InitOrderCust(o) == ((o - 1) % NumCustomers) + 1
InitOrderItems   == IIds   \* loaded orders reference every item, the worst case for Stock-Level

\* The initial value of a whole row, as a record over its columns, or Empty if it does not exist.
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
    /\ txnReq       = [t \in TxnIds |-> Empty]
    /\ txnProg      = [t \in TxnIds |-> <<>>]

----------------------------------------------------------------------------------------------------

(**************************************************************************************************)
(*                                                                                                *)
(* Actions                                                                                        *)
(*                                                                                                *)
(* `StartAndRun` begins a transaction and runs its whole body in one step; commit and abort are    *)
(* separate steps.  Collapsing the body is not an approximation, it is exact, and here is why.    *)
(* Under SI a transaction's reads are answered entirely from its begin snapshot plus its own      *)
(* prior writes, and its writes are invisible to everyone else until commit.  So the position of  *)
(* a body operation within the interval [begin, commit] is unobservable: no other transaction's   *)
(* behaviour depends on it.  And the MVSG that decides conflict serializability is built only     *)
(* from each transaction's begin time, commit time, read key set and write key set -- never from  *)
(* the interleaving of body operations.                                                           *)
(*                                                                                                *)
(* The argument relies on one thing that is easy to get wrong, and so is checked rather than      *)
(* assumed: no TPC-C transaction reads an item it has already written (`NoReadAfterWrite`).  If   *)
(* that held only approximately, evaluating the whole body against the begin snapshot would be    *)
(* wrong.                                                                                         *)
(**************************************************************************************************)

Unused(tid) == ~\E op \in SI!Range(txnHistory) : op.txnId = tid

\* Fold a program's writes into a snapshot, giving the transaction's final snapshot.  Written
\* without recursion: for each key, the value is that of the *last* write to it in `ops` (or
\* snap[k] if there is none).  Since a program writes each key at most once, this equals the
\* sequential fold.  LastW(k) picks the highest index of a write to k.
ApplyWrites(snap, ops) ==
    LET LastW(k) ==
            CHOOSE i \in DOMAIN ops :
                ops[i].type = "write" /\ ops[i].key = k
                /\ \A j \in DOMAIN ops : (ops[j].type = "write" /\ ops[j].key = k) => j =< i
        WKeys == {ops[i].key : i \in DOMAIN ops}
    IN  [k \in DOMAIN snap \cup WKeys |->
            IF \E i \in DOMAIN ops : ops[i].type = "write" /\ ops[i].key = k
            THEN ops[LastW(k)].val
            ELSE snap[k]]

(*----------------------------------------------------------------------------------------------*)
(* Begin a transaction and run its whole body in one step.                                        *)
(*                                                                                               *)
(* The begin half is exactly `SI!StartTxn` -- snapshot the committed store, append a `begin`     *)
(* event, join the running set, tick the clock.  It is inlined only because the body's events    *)
(* must be appended to `txnHistory` in the same step.                                            *)
(*----------------------------------------------------------------------------------------------*)
StartAndRun(tid, req) ==
    /\ Unused(tid)
    /\ ReqEnabled(req, dataStore)
    /\ LET prog    == ProgramFor(tid, req, dataStore)
           beginOp == [type |-> "begin", txnId |-> tid, time |-> clock + 1]
           events  == [i \in 1..Len(prog) |-> Merge(prog[i], [txnId |-> tid])]
       IN /\ txnHistory'   = txnHistory \o <<beginOp>> \o events
          /\ txnSnapshots' = [txnSnapshots EXCEPT ![tid] = ApplyWrites(dataStore, prog)]
          /\ txnProg'      = [txnProg EXCEPT ![tid] = prog]
    /\ runningTxns' = runningTxns \cup {[id |-> tid, startTime |-> clock + 1, commitTime |-> Empty]}
    /\ clock' = clock + 1
    /\ txnReq' = [txnReq EXCEPT ![tid] = req]
    /\ UNCHANGED <<dataStore>>

(*----------------------------------------------------------------------------------------------*)
(* Commit / abort are `SI!CommitTxn` and `SI!AbortTxn` verbatim: First-Committer-Wins decides,   *)
(* and a transaction aborts exactly when a concurrent transaction already committed a write to   *)
(* an item it intends to write.                                                                  *)
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
(* THE MAIN QUESTION.  Is the history this TPC-C workload produces under snapshot isolation       *)
(* conflict serializable?  `SI!IsConflictSerializable` builds the multi-version serialization     *)
(* graph over committed transactions (ww, wr and rw edges) and asks whether it is acyclic.        *)
(**************************************************************************************************)
\* Serializable == SI!IsConflictSerializable(txnHistory)

\* Equivalent to Serializable, but detects cycles via the path-based check
\* (SI!IsCycleViaPath) instead of the recursive one.
SerializableViaPath == SI!IsConflictSerializableViaPath(txnHistory)


TypeOK ==
    /\ clock \in Nat
    /\ DOMAIN dataStore = Keys
    /\ runningTxns \subseteq [id : TxnIds, startTime : Nat, commitTime : Nat \cup {Empty}]
    /\ txnReq \in [TxnIds -> Requests \cup {Empty}]

=====================================================================================================
