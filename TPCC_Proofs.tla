---------------------------- MODULE TPCC_Proofs ----------------------------
(***************************************************************************)
(* A TLAPS proof that SerializableViaPath is an invariant of TPCC, under   *)
(* column-granularity conflict detection.                                  *)
(*                                                                         *)
(* Proof idea.  Give every committed transaction t a position              *)
(*                                                                         *)
(*     Pos(t) = commit time of t   if t writes some key,                   *)
(*            = begin time of t    if t is read-only,                      *)
(*                                                                         *)
(* and show that every edge t1 -> t2 of the serialization graph satisfies  *)
(* Pos(t1) < Pos(t2).  Then no path can return to its start, so the graph  *)
(* is acyclic.  WW and WR edges are easy.  For an RW edge whose source t1  *)
(* is an updater, we need t1 to commit before t2.  If t1 also writes the   *)
(* key, this is First-Committer-Wins.  Otherwise the key is one that an    *)
(* updater reads but does not write, and the TPC-C workload guarantees     *)
(* that such keys are never written concurrently:                          *)
(*                                                                         *)
(*   - New-Order's read-only keys (W_TAX, D_TAX, C_INFO, I_INFO) are       *)
(*     never written by anybody.                                           *)
(*   - Delivery's read-only keys (ORDER.hdr, ORDERLINE.items of an order   *)
(*     o that is below the district's D_NEXT_O_ID) can only be written by  *)
(*     a New-Order for order o, which either already committed, or is     *)
(*     doomed (lost the D_NEXT_O_ID conflict), or can never start.         *)
(*   - Payment reads only keys it also writes.                             *)
(***************************************************************************)
EXTENDS TPCC, TLAPS, SequenceTheorems, NaturalsInduction

ASSUME CGAssm == ColumnGranularity = TRUE

\* Restates an assumption of TPCC (so that it can be cited by name).
ASSUME InitOrdersAssm == InitOrders \in 0..MaxOrders

\* The initial DISTRICT row is not the "no row" value.
ASSUME EmptyAssm == Empty # [tax |-> Tag, ytd |-> Tag, nextoid |-> InitOrders + 1]

(***************************************************************************)
(* Notation                                                                *)
(***************************************************************************)

NK(w, d)     == Item(DistKey(w, d), "nextoid")
NOK(w, d, o) == Item(NewOrdKey(w, d, o), "row")

UpdTypes == {"NewOrder", "Payment", "Delivery"}

Ops(h) == SI!Range(h)

Started(h, t)   == \E op \in Ops(h) : op.txnId = t
Committed(h, t) == \E op \in Ops(h) : op.txnId = t /\ op.type = "commit"
Aborted(h, t)   == \E op \in Ops(h) : op.txnId = t /\ op.type = "abort"

BT(h, t) == SI!BeginOp(h, t).time
CT(h, t) == SI!CommitOp(h, t).time

RunIds(R) == {r.id : r \in R}

\* Keys written by a body, restricted to the key universe (as in the history).
KWB(B)  == {k \in Keys : \E wop \in B.writes : wop.key = k}
\* Keys read but not written by a body.
RNWB(B) == (B.reads \cap Keys) \ KWB(B)

KW(P, t) == KWB(P[t])

Doomed(h, P, t) ==
    \E c \in Ops(h) : /\ c.type = "commit"
                      /\ c.time > BT(h, t)
                      /\ KW(P, t) \cap c.updatedKeys # {}

WV(B, k) == (CHOOSE wop \in B.writes : wop.key = k).val

(***************************************************************************)
(* Facts about the TPC-C bodies.                                           *)
(***************************************************************************)

Static(req, B) ==
    /\ req \in Requests
    /\ req.type \notin UpdTypes => B.writes = {}
    /\ req.type \in {"NewOrder", "Payment"} => \A k \in RNWB(B) : k.col \in {"tax", "info"}
    /\ req.type = "Delivery" =>
          \A k \in RNWB(B) : /\ k.tbl \in {"ORDER", "ORDERLINE"}
                             /\ k.col \in {"hdr", "items"}
                             /\ k.w \in WIds /\ k.d \in DIds /\ k.o \in OIds
    /\ \A wop \in B.writes : wop.key.col \notin {"tax", "info"}
    /\ req.type # "NewOrder" =>
          \A wop \in B.writes :
              /\ ~(wop.key.tbl = "DIST" /\ wop.key.col = "nextoid")
              /\ ~(wop.key.tbl \in {"ORDER", "ORDERLINE"} /\ wop.key.col \in {"hdr", "items"})
              /\ wop.key.tbl = "NEWORDER" => wop.val = Empty

NOStatic(req, B, o) ==
    /\ NK(req.w, req.d) \in KWB(B)
    /\ \A wop \in B.writes :
          (wop.key.tbl = "DIST" /\ wop.key.col = "nextoid") =>
              wop.key = NK(req.w, req.d) /\ wop.val = o + 1
    /\ \A wop \in B.writes :
          wop.key.tbl \in {"ORDER", "ORDERLINE", "NEWORDER"} =>
              wop.key.w = req.w /\ wop.key.d = req.d /\ wop.key.o = o

DelDyn(req, B, store) ==
    req.type = "Delivery" => \A k \in RNWB(B) : k.o < store[NK(k.w, k.d)]

(***************************************************************************)
(* The inductive invariant.                                                *)
(***************************************************************************)

TypeInv ==
    /\ clock \in Nat
    /\ txnHistory \in Seq(Ops(txnHistory))
    /\ DOMAIN dataStore = Keys
    /\ DOMAIN txnProg = TxnIds
    /\ DOMAIN txnReq = TxnIds
    /\ DOMAIN txnSnapshots = TxnIds

HistInv ==
    /\ \A op \in Ops(txnHistory) :
          /\ op.txnId \in TxnIds
          /\ op.type \in {"begin", "body", "commit", "abort"}
          /\ op.type = "body" => /\ op.reads  = txnProg[op.txnId].reads
                                 /\ op.writes = txnProg[op.txnId].writes
          /\ op.type \in {"begin", "commit", "abort"} => op.time \in Nat /\ op.time =< clock
          /\ op.type = "commit" => /\ op.updatedKeys = KW(txnProg, op.txnId)
                                   /\ BT(txnHistory, op.txnId) < op.time
    /\ \A op1, op2 \in Ops(txnHistory) :
          op1.txnId = op2.txnId /\ op1.type = op2.type => op1 = op2
    /\ \A t \in TxnIds : Started(txnHistory, t) =>
          /\ \E op \in Ops(txnHistory) : op.txnId = t /\ op.type = "begin"
          /\ \E op \in Ops(txnHistory) : op.txnId = t /\ op.type = "body"
    /\ \A r \in runningTxns :
          /\ r.id \in TxnIds
          /\ Started(txnHistory, r.id)
          /\ r.startTime = BT(txnHistory, r.id)
          /\ ~Committed(txnHistory, r.id)
          /\ ~Aborted(txnHistory, r.id)

SnapInv ==
    \A t \in TxnIds : Started(txnHistory, t) =>
        \A k \in KW(txnProg, t) : txnSnapshots[t][k] = WV(txnProg[t], k)

DataInvS(S) ==
    /\ \A w \in WIds, d \in DIds : S[NK(w, d)] \in Nat
    /\ \A w \in WIds, d \in DIds, o \in OIds :
          S[NOK(w, d, o)] # Empty => o < S[NK(w, d)]

DataInv == DataInvS(dataStore)

BodyInv ==
    \A t \in TxnIds : Started(txnHistory, t) =>
        /\ Static(txnReq[t], txnProg[t])
        /\ DelDyn(txnReq[t], txnProg[t], dataStore)
        /\ txnReq[t].type = "NewOrder" =>
              \E o \in OIds :
                  /\ NOStatic(txnReq[t], txnProg[t], o)
                  /\ (t \in RunIds(runningTxns) /\ ~Doomed(txnHistory, txnProg, t)) =>
                        dataStore[NK(txnReq[t].w, txnReq[t].d)] = o

SafeInv ==
    /\ \A t1 \in RunIds(runningTxns) : txnReq[t1].type \in UpdTypes =>
          \A k \in RNWB(txnProg[t1]) : \A y \in RunIds(runningTxns) :
              (y # t1 /\ k \in KW(txnProg, y)) => Doomed(txnHistory, txnProg, y)
    /\ \A t1 \in RunIds(runningTxns) : txnReq[t1].type \in UpdTypes =>
          \A k \in RNWB(txnProg[t1]) : \A y \in TxnIds :
              (Committed(txnHistory, y) /\ k \in KW(txnProg, y)) =>
                  CT(txnHistory, y) < BT(txnHistory, t1)

RWInv ==
    \A t1, t2 \in TxnIds :
        /\ Committed(txnHistory, t1) /\ Committed(txnHistory, t2) /\ t1 # t2
        /\ KW(txnProg, t1) # {}
        /\ \E k \in KW(txnProg, t2) : k \in txnProg[t1].reads
        /\ BT(txnHistory, t1) < CT(txnHistory, t2)
        => CT(txnHistory, t1) < CT(txnHistory, t2)

Inv == TypeInv /\ HistInv /\ SnapInv /\ DataInv /\ BodyInv /\ SafeInv /\ RWInv

----------------------------------------------------------------------------
(***************************************************************************)
(* Basic lemmas about keys.                                                *)
(***************************************************************************)

LEMMA ItemFields ==
    ASSUME NEW b, NEW c
    PROVE  /\ Item(b, c).col = c
           /\ \A f \in DOMAIN b : f # "col" => Item(b, c)[f] = b[f]
  BY CGAssm DEF Item

LEMMA KeyFields ==
    /\ \A w, d, c : /\ Item(DistKey(w, d), c).tbl = "DIST"
                    /\ Item(DistKey(w, d), c).w = w
                    /\ Item(DistKey(w, d), c).d = d
                    /\ Item(DistKey(w, d), c).col = c
    /\ \A w, c : /\ Item(WhKey(w), c).tbl = "WH"
                 /\ Item(WhKey(w), c).col = c
    /\ \A w, d, x, c : /\ Item(CustKey(w, d, x), c).tbl = "CUST"
                       /\ Item(CustKey(w, d, x), c).col = c
    /\ \A i, c : /\ Item(ItemKey(i), c).tbl = "ITEM"
                 /\ Item(ItemKey(i), c).col = c
    /\ \A w, i, c : /\ Item(StockKey(w, i), c).tbl = "STOCK"
                    /\ Item(StockKey(w, i), c).col = c
    /\ \A w, d, o, c : /\ Item(OrderKey(w, d, o), c).tbl = "ORDER"
                       /\ Item(OrderKey(w, d, o), c).w = w
                       /\ Item(OrderKey(w, d, o), c).d = d
                       /\ Item(OrderKey(w, d, o), c).o = o
                       /\ Item(OrderKey(w, d, o), c).col = c
    /\ \A w, d, o, c : /\ Item(NewOrdKey(w, d, o), c).tbl = "NEWORDER"
                       /\ Item(NewOrdKey(w, d, o), c).w = w
                       /\ Item(NewOrdKey(w, d, o), c).d = d
                       /\ Item(NewOrdKey(w, d, o), c).o = o
                       /\ Item(NewOrdKey(w, d, o), c).col = c
    /\ \A w, d, o, c : /\ Item(OrdLineKey(w, d, o), c).tbl = "ORDERLINE"
                       /\ Item(OrdLineKey(w, d, o), c).w = w
                       /\ Item(OrdLineKey(w, d, o), c).d = d
                       /\ Item(OrdLineKey(w, d, o), c).o = o
                       /\ Item(OrdLineKey(w, d, o), c).col = c
    /\ \A x, c : /\ Item(HistKey(x), c).tbl = "HIST"
                 /\ Item(HistKey(x), c).col = c
  BY CGAssm DEF Item, DistKey, WhKey, CustKey, ItemKey, StockKey, OrderKey,
                NewOrdKey, OrdLineKey, HistKey

LEMMA NKFields ==
    \A w, d : NK(w, d).tbl = "DIST" /\ NK(w, d).col = "nextoid" /\ NK(w, d).w = w /\ NK(w, d).d = d
  BY KeyFields DEF NK

LEMMA NKInj ==
    \A w1, d1, w2, d2 : NK(w1, d1) = NK(w2, d2) => w1 = w2 /\ d1 = d2
  BY NKFields

LEMMA NOKFields ==
    \A w, d, o : NOK(w, d, o).tbl = "NEWORDER" /\ NOK(w, d, o).w = w /\ NOK(w, d, o).d = d /\ NOK(w, d, o).o = o
  BY KeyFields DEF NOK

LEMMA NKInKeys ==
    \A w \in WIds, d \in DIds : NK(w, d) \in Keys
  <1> SUFFICES ASSUME NEW w \in WIds, NEW d \in DIds PROVE NK(w, d) \in Keys
    OBVIOUS
  <1>1. DistKey(w, d) \in RowKeys
    <2>1. <<w, d>> \in WIds \X DIds /\ DistKey(w, d) = DistKey(<<w, d>>[1], <<w, d>>[2])
      OBVIOUS
    <2> QED
      BY <2>1 DEF RowKeys
  <1>2. "nextoid" \in ColsOf(DistKey(w, d).tbl)
    BY DEF ColsOf, DistKey
  <1> QED
    BY <1>1, <1>2, CGAssm DEF Keys, NK

LEMMA NOKInKeys ==
    \A w \in WIds, d \in DIds, o \in OIds : NOK(w, d, o) \in Keys
  <1> SUFFICES ASSUME NEW w \in WIds, NEW d \in DIds, NEW o \in OIds PROVE NOK(w, d, o) \in Keys
    OBVIOUS
  <1>1. NewOrdKey(w, d, o) \in RowKeys
    <2>1. <<w, d, o>> \in WIds \X DIds \X OIds /\ NewOrdKey(w, d, o) = NewOrdKey(<<w, d, o>>[1], <<w, d, o>>[2], <<w, d, o>>[3])
      OBVIOUS
    <2> QED
      BY <2>1 DEF RowKeys
  <1>2. "row" \in ColsOf(NewOrdKey(w, d, o).tbl)
    BY DEF ColsOf, NewOrdKey
  <1> QED
    BY <1>1, <1>2, CGAssm DEF Keys, NOK

(***************************************************************************)
(* Generic lemmas about histories.                                         *)
(***************************************************************************)

LEMMA SeqInOwnRange ==
    ASSUME NEW S, NEW s \in Seq(S)
    PROVE  s \in Seq(Ops(s))
  <1>0. Len(s) \in Nat /\ s \in [1..Len(s) -> S] /\ DOMAIN s = 1..Len(s)
    BY LenProperties
  <1>1. \A i \in 1..Len(s) : s[i] \in Ops(s)
    BY <1>0 DEF Ops, SI!Range
  <1>2. s = [i \in 1..Len(s) |-> s[i]]
    BY <1>0
  <1>3. [i \in 1..Len(s) |-> s[i]] \in Seq(Ops(s))
    BY <1>0, <1>1, IsASeq
  <1> QED
    BY <1>2, <1>3

LEMMA RangeAppend ==
    ASSUME NEW S, NEW s \in Seq(S), NEW e
    PROVE  /\ Ops(Append(s, e)) = Ops(s) \cup {e}
           /\ Append(s, e) \in Seq(S \cup {e})
  <1>1. s \in Seq(S \cup {e})
    BY SeqDef
  <1>2. Append(s, e) \in Seq(S \cup {e}) /\ Len(Append(s, e)) = Len(s) + 1
    BY <1>1, AppendProperties
  <1>3. \A i \in 1..Len(s) : Append(s, e)[i] = s[i]
    BY <1>1, AppendProperties
  <1>4. Append(s, e)[Len(s)+1] = e
    BY <1>1, AppendProperties
  <1>5. DOMAIN Append(s, e) = 1..Len(s)+1 /\ DOMAIN s = 1..Len(s)
    BY <1>2, LenProperties
  <1> QED
    BY <1>2, <1>3, <1>4, <1>5 DEF Ops, SI!Range

LEMMA RangeConcat2 ==
    ASSUME NEW S, NEW s \in Seq(S), NEW a, NEW b
    PROVE  /\ Ops(s \o <<a, b>>) = Ops(s) \cup {a, b}
           /\ s \o <<a, b>> \in Seq(S \cup {a, b})
  <1>1. s \in Seq(S \cup {a, b}) /\ <<a, b>> \in Seq(S \cup {a, b})
    BY SeqDef
  <1>2. /\ s \o <<a, b>> \in Seq(S \cup {a, b})
        /\ Len(s \o <<a, b>>) = Len(s) + 2
        /\ \A i \in 1 .. Len(s) + 2 :
              (s \o <<a, b>>)[i] = IF i =< Len(s) THEN s[i] ELSE <<a, b>>[i - Len(s)]
    BY <1>1, ConcatProperties
  <1>5. DOMAIN (s \o <<a, b>>) = 1..Len(s)+2 /\ DOMAIN s = 1..Len(s)
    BY <1>2, LenProperties
  <1>6. Len(s) \in Nat
    BY LenProperties
  <1> QED
    BY <1>2, <1>5, <1>6 DEF Ops, SI!Range

UniqueOps(h) ==
    \A op1, op2 \in Ops(h) : op1.txnId = op2.txnId /\ op1.type = op2.type => op1 = op2

BodyMatch(h, P) ==
    \A op \in Ops(h) : op.type = "body" => op.reads = P[op.txnId].reads /\ op.writes = P[op.txnId].writes

LEMMA BTVal ==
    ASSUME NEW h, UniqueOps(h), NEW t, NEW b \in Ops(h), b.type = "begin", b.txnId = t
    PROVE  SI!BeginOp(h, t) = b /\ BT(h, t) = b.time
  BY DEF UniqueOps, BT, SI!BeginOp, Ops

LEMMA CTVal ==
    ASSUME NEW h, UniqueOps(h), NEW t, NEW c \in Ops(h), c.type = "commit", c.txnId = t
    PROVE  SI!CommitOp(h, t) = c /\ CT(h, t) = c.time
  BY DEF UniqueOps, CT, SI!CommitOp, Ops

LEMMA HistKeys ==
    ASSUME NEW h, NEW P, BodyMatch(h, P), NEW t, NEW bo \in Ops(h), bo.type = "body", bo.txnId = t
    PROVE  /\ SI!KeysWrittenByTxn(h, t) = KW(P, t)
           /\ \A k : SI!ReadsKey(h, t, k) <=> k \in P[t].reads
           /\ \A k : SI!WritesKey(h, t, k) <=> \E wop \in P[t].writes : wop.key = k
  <1>1. \A k : SI!ReadsKey(h, t, k) <=> k \in P[t].reads
    BY DEF BodyMatch, SI!ReadsKey, Ops
  <1>2. \A k : SI!WritesKey(h, t, k) <=> \E wop \in P[t].writes : wop.key = k
    BY DEF BodyMatch, SI!WritesKey, Ops
  <1> QED
    BY <1>1, <1>2 DEF SI!KeysWrittenByTxn, KW, KWB

(***************************************************************************)
(* A graph in which every edge strictly increases an integer potential has *)
(* no cycle.                                                               *)
(***************************************************************************)
LEMMA NoCycle ==
    ASSUME NEW E, NEW F(_),
           \A e \in E : F(e[1]) \in Int /\ F(e[2]) \in Int /\ F(e[1]) < F(e[2])
    PROVE  ~SI!IsCycleViaPath(E)
  <1> SUFFICES ASSUME NEW p \in SI!Paths(E), Len(p) > 1, p[1] = p[Len(p)]
               PROVE  FALSE
    BY DEF SI!IsCycleViaPath
  <1>1. PICK n \in 1..SI!PathBound(E) : p \in [1..n -> SI!GraphNodes(E)]
    BY DEF SI!Paths
  <1>2. Len(p) = n /\ n \in Nat
    BY <1>1
  <1>3. \A i \in 1..(n-1) : <<p[i], p[i+1]>> \in E
    BY <1>1, <1>2 DEF SI!Paths
  <1>4. \A i \in 1..(n-1) : F(p[i]) \in Int /\ F(p[i+1]) \in Int /\ F(p[i]) < F(p[i+1])
    BY <1>3
  <1> DEFINE Q(j) == j \in 2..n => F(p[1]) < F(p[j])
  <1>5. \A j \in Nat : Q(j)
    <2>1. Q(0)
      OBVIOUS
    <2>2. ASSUME NEW j \in Nat, Q(j) PROVE Q(j+1)
      <3> SUFFICES ASSUME j + 1 \in 2..n PROVE F(p[1]) < F(p[j+1])
        OBVIOUS
      <3>1. CASE j = 1
        BY <3>1, <1>4
      <3>2. CASE j # 1
        <4>1. j \in 2..n /\ j \in 1..(n-1)
          BY <3>2
        <4> QED
          BY <4>1, <2>2, <1>4, <1>1
      <3> QED
        BY <3>1, <3>2
    <2> QED
      BY <2>1, <2>2, NatInduction
  <1>6. n \in 2..n
    BY <1>2
  <1> QED
    BY <1>5, <1>6, <1>2, <1>4

(***************************************************************************)
(* The TPC-C programs under column granularity.                            *)
(***************************************************************************)

LEMMA ReqTypes ==
    ASSUME NEW req \in Requests
    PROVE  /\ req.type \in AllTxnTypes
           /\ req.type = "NewOrder" =>
                req \in [type : {"NewOrder"}, w : WIds, d : DIds, c : CIds, sw : WIds, items : NewOrderItemSets]
           /\ req.type = "Payment" =>
                req \in [type : {"Payment"}, w : WIds, d : DIds, cw : WIds, cd : DIds, c : CIds]
           /\ req.type = "OrderStatus" =>
                req \in [type : {"OrderStatus"}, w : WIds, d : DIds, c : CIds]
           /\ req.type = "Delivery" => req \in [type : {"Delivery"}, w : WIds]
           /\ req.type = "StockLevel" => req \in [type : {"StockLevel"}, w : WIds, d : DIds]
  BY DEF Requests, AllTxnTypes

LEMMA RdKeysCG ==
    \A b, cols : RdKeys(b, cols) = {Item(b, c) : c \in cols}
  BY CGAssm DEF RdKeys

LEMMA WrOpsCG ==
    \A snap, b, upd :
        WrOps(snap, b, upd) = {[type |-> "write", key |-> Item(b, c), val |-> upd[c]] : c \in DOMAIN upd}
  BY CGAssm DEF WrOps

LEMMA ColValCG ==
    \A snap, b, c : ColVal(snap, b, c) = snap[Item(b, c)]
  BY CGAssm DEF ColVal

LEMMA NOProg ==
    ASSUME NEW req \in Requests, req.type = "NewOrder", NEW snap,
           snap[NK(req.w, req.d)] \in OIds
    PROVE  LET B == NewOrderProgram(req, snap) IN
           /\ Static(req, B)
           /\ DelDyn(req, B, snap)
           /\ NOStatic(req, B, snap[NK(req.w, req.d)])
  <1> DEFINE w == req.w  d == req.d  c == req.c  sw == req.sw  items == req.items
             o == snap[NK(w, d)]
             B == NewOrderProgram(req, snap)
  <1>0. req \in [type : {"NewOrder"}, w : WIds, d : DIds, c : CIds, sw : WIds, items : NewOrderItemSets]
    BY ReqTypes
  <1>1. B.reads = {Item(WhKey(w), "tax"), Item(DistKey(w, d), "tax"), Item(DistKey(w, d), "nextoid"),
                   Item(CustKey(w, d, c), "info")}
                  \cup {Item(ItemKey(i), "info") : i \in items}
                  \cup {Item(StockKey(sw, i), "qty") : i \in items}
    BY RdKeysCG, ColValCG DEF NewOrderProgram
  <1>2. B.writes = {[type |-> "write", key |-> NK(w, d), val |-> o + 1],
                    [type |-> "write", key |-> Item(OrderKey(w, d, o), "hdr"), val |-> c],
                    [type |-> "write", key |-> Item(OrderKey(w, d, o), "carrier"), val |-> Tag],
                    [type |-> "write", key |-> Item(NewOrdKey(w, d, o), "row"), val |-> Tag],
                    [type |-> "write", key |-> Item(OrdLineKey(w, d, o), "items"), val |-> items],
                    [type |-> "write", key |-> Item(OrdLineKey(w, d, o), "delivery"), val |-> Tag]}
                   \cup {[type |-> "write", key |-> Item(StockKey(sw, i), "qty"), val |-> Tag] : i \in items}
    BY WrOpsCG, ColValCG DEF NewOrderProgram, NK
  <1>a. w \in WIds /\ d \in DIds /\ o \in OIds
    BY <1>0
  <1>b. NK(w, d) \in Keys
    BY <1>a, NKInKeys
  <1>3. Static(req, B)
    <2>1. \A k \in RNWB(B) : k.col \in {"tax", "info"}
      <3> SUFFICES ASSUME NEW k \in RNWB(B) PROVE k.col \in {"tax", "info"}
        OBVIOUS
      <3>1. k \in B.reads /\ k \in Keys /\ k \notin KWB(B)
        BY DEF RNWB
      <3>2. k # NK(w, d)
        BY <3>1, <1>2 DEF KWB
      <3>3. \A i \in items : k # Item(StockKey(sw, i), "qty")
        BY <3>1, <1>2 DEF KWB
      <3> QED
        BY <3>1, <3>2, <3>3, <1>1, KeyFields DEF NK
    <2>2. \A wop \in B.writes : wop.key.col \notin {"tax", "info"}
      BY <1>2, KeyFields, NKFields
    <2> QED
      BY <2>1, <2>2 DEF Static, UpdTypes
  <1>4. DelDyn(req, B, snap)
    BY DEF DelDyn
  <1>5. NOStatic(req, B, o)
    <2>1. NK(w, d) \in KWB(B)
      BY <1>2, <1>b DEF KWB
    <2>2. \A wop \in B.writes :
             (wop.key.tbl = "DIST" /\ wop.key.col = "nextoid") => wop.key = NK(w, d) /\ wop.val = o + 1
      BY <1>2, KeyFields
    <2>3. \A wop \in B.writes :
             wop.key.tbl \in {"ORDER", "ORDERLINE", "NEWORDER"} => wop.key.w = w /\ wop.key.d = d /\ wop.key.o = o
      BY <1>2, KeyFields, NKFields
    <2> QED
      BY <2>1, <2>2, <2>3 DEF NOStatic
  <1> QED
    BY <1>3, <1>4, <1>5

LEMMA PayProg ==
    ASSUME NEW tid, NEW req \in Requests, req.type = "Payment", NEW snap
    PROVE  LET B == PaymentProgram(tid, req, snap) IN
           Static(req, B) /\ DelDyn(req, B, snap)
  <1> DEFINE w == req.w  d == req.d  cw == req.cw  cd == req.cd  c == req.c
             B == PaymentProgram(tid, req, snap)
  <1>1. B.reads = {Item(WhKey(w), "ytd"), Item(DistKey(w, d), "ytd"), Item(CustKey(cw, cd, c), "balance")}
    BY RdKeysCG DEF PaymentProgram
  <1>2. B.writes = {[type |-> "write", key |-> Item(WhKey(w), "ytd"), val |-> Tag],
                    [type |-> "write", key |-> Item(DistKey(w, d), "ytd"), val |-> Tag],
                    [type |-> "write", key |-> Item(CustKey(cw, cd, c), "balance"), val |-> Tag],
                    [type |-> "write", key |-> Item(HistKey(tid), "row"), val |-> Tag]}
    BY WrOpsCG DEF PaymentProgram
  <1>3. RNWB(B) = {}
    BY <1>1, <1>2 DEF RNWB, KWB
  <1>4. \A wop \in B.writes :
           /\ wop.key.col \notin {"tax", "info"}
           /\ ~(wop.key.tbl = "DIST" /\ wop.key.col = "nextoid")
           /\ ~(wop.key.tbl \in {"ORDER", "ORDERLINE"} /\ wop.key.col \in {"hdr", "items"})
           /\ wop.key.tbl # "NEWORDER"
    BY <1>2, KeyFields
  <1> QED
    BY <1>3, <1>4 DEF Static, DelDyn, UpdTypes

LEMMA OSProg ==
    ASSUME NEW req \in Requests, req.type = "OrderStatus", NEW snap
    PROVE  LET B == OrderStatusProgram(req, snap) IN
           Static(req, B) /\ DelDyn(req, B, snap)
  <1>1. OrderStatusProgram(req, snap).writes = {}
    BY DEF OrderStatusProgram
  <1> QED
    BY <1>1 DEF Static, DelDyn, UpdTypes

LEMMA SLProg ==
    ASSUME NEW req \in Requests, req.type = "StockLevel", NEW snap
    PROVE  LET B == StockLevelProgram(req, snap) IN
           Static(req, B) /\ DelDyn(req, B, snap)
  <1>1. StockLevelProgram(req, snap).writes = {}
    BY DEF StockLevelProgram
  <1> QED
    BY <1>1 DEF Static, DelDyn, UpdTypes

LEMMA MinProps ==
    ASSUME NEW U \in SUBSET Nat, U # {}
    PROVE  Min(U) \in U /\ \A y \in U : Min(U) =< y
  <1> DEFINE P(m) == m \in U
  <1>1. PICK n \in U : TRUE
    OBVIOUS
  <1>1a. n \in Nat /\ P(n)
    BY <1>1
  <1> HIDE DEF P
  <1>2. \E m \in Nat : P(m) /\ \A k \in 0 .. m-1 : ~P(k)
    BY ONLY <1>1a, SmallestNatural, Isa
  <1> USE DEF P
  <1>3. PICK m \in Nat : P(m) /\ \A k \in 0 .. m-1 : ~P(k)
    BY <1>2
  <1>4. \A y \in U : m =< y
    <2> SUFFICES ASSUME NEW y \in U PROVE m =< y
      OBVIOUS
    <2>1. y \in Nat
      OBVIOUS
    <2>2. ~(y \in 0 .. m-1)
      BY <1>3
    <2> QED
      BY <2>1, <2>2, <1>3
  <1>5. \E mm \in U : \A y \in U : mm =< y
    BY <1>3, <1>4
  <1> QED
    BY <1>5 DEF Min

LEMMA DFDFacts ==
    ASSUME NEW w \in WIds, NEW d \in DIds, NEW snap, DataInvS(snap)
    PROVE  LET D == DeliveryForDistrict(w, d, snap) IN
           /\ \A wop \in D.writes :
                 /\ wop.key.col \in {"row", "carrier", "delivery", "balance"}
                 /\ wop.key.tbl \in {"NEWORDER", "ORDER", "ORDERLINE", "CUST"}
                 /\ wop.key.tbl = "NEWORDER" => wop.val = Empty
                 /\ ~(wop.key.tbl \in {"ORDER", "ORDERLINE"} /\ wop.key.col \in {"hdr", "items"})
           /\ \A k \in D.reads :
                 \/ \E wop \in D.writes : wop.key = k
                 \/ /\ k.tbl \in {"ORDER", "ORDERLINE"} /\ k.col \in {"hdr", "items"}
                    /\ k.w = w /\ k.d = d /\ k.o \in OIds /\ k.o < snap[NK(w, d)]
  <1> DEFINE U == {o \in OIds : RowExists(snap, NewOrdKey(w, d, o))}
             D == DeliveryForDistrict(w, d, snap)
  <1>1. CASE U = {}
    <2>1. D.reads = {} /\ D.writes = {}
      BY <1>1 DEF DeliveryForDistrict
    <2> QED
      BY <2>1
  <1>2. CASE U # {}
    <2> DEFINE o == Min(U)
               cust == ColVal(snap, OrderKey(w, d, o), "hdr")
    <2>0. U \subseteq Nat
      BY DEF OIds
    <2>1. o \in U
      BY <1>2, <2>0, MinProps
    <2>2. o \in OIds /\ snap[NOK(w, d, o)] # Empty
      <3>1. o \in OIds /\ RowExists(snap, NewOrdKey(w, d, o))
        BY <2>1
      <3>2. PrimaryCol(NewOrdKey(w, d, o).tbl) = "row"
        BY DEF PrimaryCol, NewOrdKey
      <3>3. RowExists(snap, NewOrdKey(w, d, o)) <=> snap[Item(NewOrdKey(w, d, o), "row")] # Empty
        BY <3>2, ColValCG DEF RowExists
      <3> QED
        BY <3>1, <3>3 DEF NOK
    <2>3. o < snap[NK(w, d)]
      BY <2>2 DEF DataInvS
    <2>4. D.reads = {Item(NewOrdKey(w, d, o), "row"), Item(OrderKey(w, d, o), "hdr"),
                     Item(OrdLineKey(w, d, o), "items"), Item(CustKey(w, d, cust), "balance")}
      BY <1>2, RdKeysCG DEF DeliveryForDistrict
    <2>5. D.writes = {[type |-> "write", key |-> Item(NewOrdKey(w, d, o), "row"), val |-> Empty],
                      [type |-> "write", key |-> Item(OrderKey(w, d, o), "carrier"), val |-> Tag],
                      [type |-> "write", key |-> Item(OrdLineKey(w, d, o), "delivery"), val |-> Tag],
                      [type |-> "write", key |-> Item(CustKey(w, d, cust), "balance"), val |-> Tag]}
      <3>1. DelOps(NewOrdKey(w, d, o)) = {[type |-> "write", key |-> Item(NewOrdKey(w, d, o), "row"), val |-> Empty]}
        BY CGAssm DEF DelOps, ColsOf, NewOrdKey
      <3> QED
        BY <1>2, <3>1, WrOpsCG DEF DeliveryForDistrict
    <2>6. \A wop \in D.writes :
                 /\ wop.key.col \in {"row", "carrier", "delivery", "balance"}
                 /\ wop.key.tbl \in {"NEWORDER", "ORDER", "ORDERLINE", "CUST"}
                 /\ wop.key.tbl = "NEWORDER" => wop.val = Empty
                 /\ ~(wop.key.tbl \in {"ORDER", "ORDERLINE"} /\ wop.key.col \in {"hdr", "items"})
      BY <2>5, KeyFields
    <2>7. \A k \in D.reads :
                 \/ \E wop \in D.writes : wop.key = k
                 \/ /\ k.tbl \in {"ORDER", "ORDERLINE"} /\ k.col \in {"hdr", "items"}
                    /\ k.w = w /\ k.d = d /\ k.o \in OIds /\ k.o < snap[NK(w, d)]
      BY <2>2, <2>3, <2>4, <2>5, KeyFields
    <2> QED
      BY <2>6, <2>7
  <1> QED
    BY <1>1, <1>2

LEMMA DelProg ==
    ASSUME NEW req \in Requests, req.type = "Delivery", NEW snap, DataInvS(snap)
    PROVE  LET B == DeliveryProgram(req, snap) IN
           Static(req, B) /\ DelDyn(req, B, snap)
  <1> DEFINE w == req.w
             B == DeliveryProgram(req, snap)
  <1>0. w \in WIds
    BY ReqTypes
  <1>1. B.reads = UNION {DeliveryForDistrict(w, d, snap).reads : d \in DIds}
        /\ B.writes = UNION {DeliveryForDistrict(w, d, snap).writes : d \in DIds}
    BY DEF DeliveryProgram
  <1>2. \A wop \in B.writes :
           /\ wop.key.col \notin {"tax", "info"}
           /\ ~(wop.key.tbl = "DIST" /\ wop.key.col = "nextoid")
           /\ ~(wop.key.tbl \in {"ORDER", "ORDERLINE"} /\ wop.key.col \in {"hdr", "items"})
           /\ wop.key.tbl = "NEWORDER" => wop.val = Empty
    <2> SUFFICES ASSUME NEW wop \in B.writes
                 PROVE  /\ wop.key.col \notin {"tax", "info"}
                        /\ ~(wop.key.tbl = "DIST" /\ wop.key.col = "nextoid")
                        /\ ~(wop.key.tbl \in {"ORDER", "ORDERLINE"} /\ wop.key.col \in {"hdr", "items"})
                        /\ wop.key.tbl = "NEWORDER" => wop.val = Empty
      OBVIOUS
    <2>1. PICK d \in DIds : wop \in DeliveryForDistrict(w, d, snap).writes
      BY <1>1
    <2> QED
      BY <2>1, <1>0, DFDFacts
  <1>3. \A k \in RNWB(B) : /\ k.tbl \in {"ORDER", "ORDERLINE"}
                           /\ k.col \in {"hdr", "items"}
                           /\ k.w \in WIds /\ k.d \in DIds /\ k.o \in OIds
                           /\ k.o < snap[NK(k.w, k.d)]
    <2> SUFFICES ASSUME NEW k \in RNWB(B)
                 PROVE  /\ k.tbl \in {"ORDER", "ORDERLINE"}
                        /\ k.col \in {"hdr", "items"}
                        /\ k.w \in WIds /\ k.d \in DIds /\ k.o \in OIds
                        /\ k.o < snap[NK(k.w, k.d)]
      OBVIOUS
    <2>1. k \in B.reads /\ k \in Keys /\ k \notin KWB(B)
      BY DEF RNWB
    <2>2. PICK d \in DIds : k \in DeliveryForDistrict(w, d, snap).reads
      BY <2>1, <1>1
    <2>3. ~\E wop \in DeliveryForDistrict(w, d, snap).writes : wop.key = k
      BY <2>1, <1>1 DEF KWB
    <2> QED
      BY <2>2, <2>3, <1>0, DFDFacts
  <1> QED
    BY <1>2, <1>3 DEF Static, DelDyn, UpdTypes

LEMMA ProgFor ==
    ASSUME NEW tid, NEW req \in Requests, NEW snap, DataInvS(snap), ReqEnabled(req, snap)
    PROVE  LET B == ProgramFor(tid, req, snap) IN
           /\ Static(req, B)
           /\ DelDyn(req, B, snap)
           /\ req.type = "NewOrder" =>
                 /\ snap[NK(req.w, req.d)] \in OIds
                 /\ NOStatic(req, B, snap[NK(req.w, req.d)])
  <1>0. req.type \in AllTxnTypes
    BY ReqTypes
  <1>1. CASE req.type = "NewOrder"
    <2>1. snap[NK(req.w, req.d)] \in OIds
      BY <1>1, ColValCG DEF ReqEnabled, NewOrderEnabled, NK
    <2>2. ProgramFor(tid, req, snap) = NewOrderProgram(req, snap)
      BY <1>1 DEF ProgramFor
    <2> QED
      BY <1>1, <2>1, <2>2, NOProg
  <1>2. CASE req.type = "Payment"
    <2>2. ProgramFor(tid, req, snap) = PaymentProgram(tid, req, snap)
      BY <1>2 DEF ProgramFor
    <2> QED
      BY <1>2, <2>2, PayProg
  <1>3. CASE req.type = "OrderStatus"
    <2>2. ProgramFor(tid, req, snap) = OrderStatusProgram(req, snap)
      BY <1>3 DEF ProgramFor
    <2> QED
      BY <1>3, <2>2, OSProg
  <1>4. CASE req.type = "Delivery"
    <2>2. ProgramFor(tid, req, snap) = DeliveryProgram(req, snap)
      BY <1>4 DEF ProgramFor
    <2> QED
      BY <1>4, <2>2, DelProg
  <1>5. CASE req.type = "StockLevel"
    <2>2. ProgramFor(tid, req, snap) = StockLevelProgram(req, snap)
      BY <1>5 DEF ProgramFor
    <2> QED
      BY <1>5, <2>2, SLProg
  <1> QED
    BY <1>0, <1>1, <1>2, <1>3, <1>4, <1>5 DEF AllTxnTypes

----------------------------------------------------------------------------
(***************************************************************************)
(* The initial state.                                                      *)
(***************************************************************************)

LEMMA InitStoreFacts ==
    ASSUME Init
    PROVE  DataInv
  <1>1. \A w \in WIds, d \in DIds : dataStore[NK(w, d)] = InitOrders + 1
    <2> SUFFICES ASSUME NEW w \in WIds, NEW d \in DIds PROVE dataStore[NK(w, d)] = InitOrders + 1
      OBVIOUS
    <2>1. NK(w, d) \in Keys
      BY NKInKeys
    <2> DEFINE k == NK(w, d)
               base == [f \in (DOMAIN k) \ {"col"} |-> k[f]]
    <2>2. "tbl" \in (DOMAIN k) \ {"col"} /\ k["tbl"] = "DIST" /\ k.col = "nextoid"
      BY CGAssm DEF NK, Item, DistKey
    <2>3. base.tbl = "DIST"
      BY <2>2
    <2>4. InitRow(base) = [tax |-> Tag, ytd |-> Tag, nextoid |-> InitOrders + 1]
      BY <2>3 DEF InitRow
    <2>5. dataStore[k] = IF InitRow(base) = Empty THEN Empty ELSE InitRow(base)[k.col]
      BY <2>1, CGAssm DEF Init, InitStore
    <2> QED
      BY <2>2, <2>4, <2>5, EmptyAssm
  <1>2. \A w \in WIds, d \in DIds, o \in OIds : dataStore[NOK(w, d, o)] # Empty => o =< InitOrders
    <2> SUFFICES ASSUME NEW w \in WIds, NEW d \in DIds, NEW o \in OIds,
                        dataStore[NOK(w, d, o)] # Empty
                 PROVE  o =< InitOrders
      OBVIOUS
    <2>1. NOK(w, d, o) \in Keys
      BY NOKInKeys
    <2> DEFINE k == NOK(w, d, o)
               base == [f \in (DOMAIN k) \ {"col"} |-> k[f]]
    <2>2. /\ "tbl" \in (DOMAIN k) \ {"col"} /\ k["tbl"] = "NEWORDER"
          /\ "o" \in (DOMAIN k) \ {"col"} /\ k["o"] = o
      BY CGAssm DEF NOK, Item, NewOrdKey
    <2>3. base.tbl = "NEWORDER" /\ base.o = o
      BY <2>2
    <2>4. InitRow(base) = IF o =< InitOrders THEN [row |-> Tag] ELSE Empty
      BY <2>3 DEF InitRow
    <2>5. dataStore[k] = IF InitRow(base) = Empty THEN Empty ELSE InitRow(base)[k.col]
      BY <2>1, CGAssm DEF Init, InitStore
    <2> QED
      BY <2>4, <2>5
  <1>3. InitOrders \in Nat
    BY InitOrdersAssm
  <1> QED
    BY <1>1, <1>2, <1>3 DEF DataInv, DataInvS, OIds

THEOREM InitInv ==
    Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1>1. Ops(txnHistory) = {}
    BY DEF Init, Ops, SI!Range
  <1>2. TypeInv
    <2>1. DOMAIN dataStore = Keys
      BY CGAssm DEF Init, InitStore
    <2>2. txnHistory \in Seq(Ops(txnHistory))
      BY EmptySeq DEF Init
    <2> QED
      BY <2>1, <2>2 DEF Init, TypeInv
  <1>3. HistInv
    BY <1>1 DEF HistInv, Init, Started
  <1>4. SnapInv /\ BodyInv
    BY <1>1 DEF SnapInv, BodyInv, Started
  <1>5. SafeInv
    BY DEF SafeInv, Init, RunIds
  <1>6. RWInv
    BY <1>1 DEF RWInv, Committed
  <1> QED
    BY <1>2, <1>3, <1>4, <1>5, <1>6, InitStoreFacts DEF Inv

----------------------------------------------------------------------------
(***************************************************************************)
(* The invariant implies serializability.                                  *)
(***************************************************************************)

Pos(t) == IF KW(txnProg, t) # {} THEN CT(txnHistory, t) ELSE BT(txnHistory, t)

LEMMA CommittedFacts ==
    ASSUME TypeInv, HistInv, NEW t, Committed(txnHistory, t)
    PROVE  /\ t \in TxnIds
           /\ BT(txnHistory, t) \in Nat
           /\ CT(txnHistory, t) \in Nat
           /\ BT(txnHistory, t) < CT(txnHistory, t)
           /\ CT(txnHistory, t) =< clock
           /\ SI!KeysWrittenByTxn(txnHistory, t) = KW(txnProg, t)
           /\ \A k : SI!ReadsKey(txnHistory, t, k) <=> k \in txnProg[t].reads
           /\ \A k : SI!WritesKey(txnHistory, t, k) <=> \E wop \in txnProg[t].writes : wop.key = k
  <1>1. PICK c \in Ops(txnHistory) : c.txnId = t /\ c.type = "commit"
    BY DEF Committed
  <1>2. t \in TxnIds /\ Started(txnHistory, t)
    BY <1>1 DEF HistInv, Started
  <1>3. PICK b \in Ops(txnHistory) : b.txnId = t /\ b.type = "begin"
    BY <1>2 DEF HistInv
  <1>4. PICK bo \in Ops(txnHistory) : bo.txnId = t /\ bo.type = "body"
    BY <1>2 DEF HistInv
  <1>5. UniqueOps(txnHistory) /\ BodyMatch(txnHistory, txnProg)
    BY DEF HistInv, UniqueOps, BodyMatch
  <1>6. BT(txnHistory, t) = b.time /\ CT(txnHistory, t) = c.time
    BY <1>1, <1>3, <1>5, BTVal, CTVal
  <1>7. b.time \in Nat /\ c.time \in Nat /\ c.time =< clock /\ BT(txnHistory, t) < c.time
    BY <1>1, <1>3 DEF HistInv
  <1> QED
    BY <1>2, <1>4, <1>5, <1>6, <1>7, HistKeys

THEOREM InvSerializable ==
    Inv => SerializableViaPath
  <1> SUFFICES ASSUME Inv PROVE SerializableViaPath
    OBVIOUS
  <1> DEFINE E == SI!SerializationGraph(txnHistory)
  <1>1. \A e \in E : Pos(e[1]) \in Int /\ Pos(e[2]) \in Int /\ Pos(e[1]) < Pos(e[2])
    <2> SUFFICES ASSUME NEW e \in E
                 PROVE  Pos(e[1]) \in Int /\ Pos(e[2]) \in Int /\ Pos(e[1]) < Pos(e[2])
      OBVIOUS
    <2> DEFINE t1 == e[1]  t2 == e[2]
    <2>0. /\ e \in SI!CommittedTxns(txnHistory) \X SI!CommittedTxns(txnHistory)
          /\ t1 # t2
          /\ \/ SI!WWDependency(txnHistory, t1, t2)
             \/ SI!WRDependency(txnHistory, t1, t2)
             \/ SI!RWDependency(txnHistory, t1, t2)
      BY DEF SI!SerializationGraph
    <2>a. \A x \in SI!CommittedTxns(txnHistory) : Committed(txnHistory, x)
      BY DEF SI!CommittedTxns, Committed, Ops
    <2>1. /\ Committed(txnHistory, t1) /\ Committed(txnHistory, t2) /\ t1 # t2
          /\ \/ SI!WWDependency(txnHistory, t1, t2)
             \/ SI!WRDependency(txnHistory, t1, t2)
             \/ SI!RWDependency(txnHistory, t1, t2)
      BY <2>0, <2>a
    <2>2. /\ t1 \in TxnIds /\ BT(txnHistory, t1) \in Nat /\ CT(txnHistory, t1) \in Nat
          /\ BT(txnHistory, t1) < CT(txnHistory, t1)
          /\ \A k : SI!ReadsKey(txnHistory, t1, k) <=> k \in txnProg[t1].reads
          /\ \A k : SI!WritesKey(txnHistory, t1, k) <=> \E wop \in txnProg[t1].writes : wop.key = k
      BY <2>1, CommittedFacts DEF Inv
    <2>3. /\ t2 \in TxnIds /\ BT(txnHistory, t2) \in Nat /\ CT(txnHistory, t2) \in Nat
          /\ BT(txnHistory, t2) < CT(txnHistory, t2)
          /\ \A k : SI!ReadsKey(txnHistory, t2, k) <=> k \in txnProg[t2].reads
          /\ \A k : SI!WritesKey(txnHistory, t2, k) <=> \E wop \in txnProg[t2].writes : wop.key = k
      BY <2>1, CommittedFacts DEF Inv
    <2>4. Pos(t1) \in Int /\ Pos(t2) \in Int
      BY <2>2, <2>3 DEF Pos
    <2>5. CASE SI!WWDependency(txnHistory, t1, t2)
      <3>1. PICK k \in Keys : SI!WritesKey(txnHistory, t1, k) /\ SI!WritesKey(txnHistory, t2, k)
        BY <2>5 DEF SI!WWDependency
      <3>2. k \in KW(txnProg, t1) /\ k \in KW(txnProg, t2)
        BY <3>1, <2>2, <2>3 DEF KW, KWB
      <3>3. CT(txnHistory, t1) < CT(txnHistory, t2)
        BY <2>5 DEF SI!WWDependency, CT
      <3> QED
        BY <3>2, <3>3, <2>4 DEF Pos
    <2>6. CASE SI!WRDependency(txnHistory, t1, t2)
      <3>1. PICK k \in Keys : SI!WritesKey(txnHistory, t1, k) /\ SI!ReadsKey(txnHistory, t2, k)
        BY <2>6 DEF SI!WRDependency
      <3>2. k \in KW(txnProg, t1)
        BY <3>1, <2>2 DEF KW, KWB
      <3>3. CT(txnHistory, t1) < BT(txnHistory, t2)
        BY <2>6 DEF SI!WRDependency, CT, BT
      <3> QED
        BY <3>2, <3>3, <2>2, <2>3, <2>4 DEF Pos
    <2>7. CASE SI!RWDependency(txnHistory, t1, t2)
      <3>1. PICK k \in Keys : SI!ReadsKey(txnHistory, t1, k) /\ SI!WritesKey(txnHistory, t2, k)
        BY <2>7 DEF SI!RWDependency
      <3>2. k \in KW(txnProg, t2) /\ k \in txnProg[t1].reads
        BY <3>1, <2>2, <2>3 DEF KW, KWB
      <3>3. BT(txnHistory, t1) < CT(txnHistory, t2)
        BY <2>7 DEF SI!RWDependency, CT, BT
      <3>4. CASE KW(txnProg, t1) = {}
        BY <3>2, <3>3, <3>4, <2>4 DEF Pos
      <3>5. CASE KW(txnProg, t1) # {}
        <4>1. CT(txnHistory, t1) < CT(txnHistory, t2)
          BY <3>2, <3>3, <3>5, <2>1, <2>2, <2>3 DEF Inv, RWInv
        <4> QED
          BY <4>1, <3>2, <3>5, <2>4 DEF Pos
      <3> QED
        BY <3>4, <3>5
    <2> QED
      BY <2>1, <2>4, <2>5, <2>6, <2>7
  <1>2. ~SI!IsCycleViaPath(E)
    BY <1>1, NoCycle
  <1> QED
    BY <1>2 DEF SerializableViaPath, SI!SerializableViaPath, SI!IsConflictSerializableViaPath

----------------------------------------------------------------------------
(***************************************************************************)
(* Lemmas used by all the step proofs.                                     *)
(***************************************************************************)

LEMMA StartedFacts ==
    ASSUME TypeInv, HistInv, NEW t, Started(txnHistory, t)
    PROVE  /\ t \in TxnIds
           /\ \E b \in Ops(txnHistory) : b.txnId = t /\ b.type = "begin" /\ b.time = BT(txnHistory, t)
           /\ BT(txnHistory, t) \in Nat
           /\ BT(txnHistory, t) =< clock
           /\ \E bo \in Ops(txnHistory) : bo.txnId = t /\ bo.type = "body"
  <1>1. t \in TxnIds
    BY DEF HistInv, Started
  <1>2. PICK b \in Ops(txnHistory) : b.txnId = t /\ b.type = "begin"
    BY <1>1 DEF HistInv
  <1>3. UniqueOps(txnHistory)
    BY DEF HistInv, UniqueOps
  <1>4. BT(txnHistory, t) = b.time
    BY <1>2, <1>3, BTVal
  <1>5. b.time \in Nat /\ b.time =< clock
    BY <1>2 DEF HistInv
  <1> QED
    BY <1>1, <1>2, <1>4, <1>5 DEF HistInv

LEMMA RunningFacts ==
    ASSUME TypeInv, HistInv, NEW t \in RunIds(runningTxns)
    PROVE  /\ t \in TxnIds
           /\ Started(txnHistory, t)
           /\ ~Committed(txnHistory, t)
           /\ ~Aborted(txnHistory, t)
           /\ \E r \in runningTxns : r.id = t /\ r.startTime = BT(txnHistory, t)
  BY DEF HistInv, RunIds

\* Extending a history (with unique ops) does not change begin / commit times.
LEMMA ExtendTimes ==
    ASSUME NEW h, NEW h2, UniqueOps(h2), Ops(h) \subseteq Ops(h2), NEW t
    PROVE  /\ \A b \in Ops(h) : b.type = "begin" /\ b.txnId = t => BT(h2, t) = b.time
           /\ \A c \in Ops(h) : c.type = "commit" /\ c.txnId = t => CT(h2, t) = c.time
  BY BTVal, CTVal

----------------------------------------------------------------------------
(***************************************************************************)
(* AbortTxn preserves the invariant.                                       *)
(***************************************************************************)

THEOREM AbortStep ==
    ASSUME Inv, NEW tid \in TxnIds, AbortTxn(tid)
    PROVE  Inv'
  <1> DEFINE h == txnHistory
             aop == [type |-> "abort", txnId |-> tid, time |-> clock + 1]
  <1> USE DEF Inv
  <1>0. /\ tid \in RunIds(runningTxns)
        /\ txnHistory' = Append(h, aop)
        /\ runningTxns' = {r \in runningTxns : r.id # tid}
        /\ clock' = clock + 1
        /\ UNCHANGED <<dataStore, txnSnapshots, txnProg, txnReq>>
    BY DEF AbortTxn, SI!AbortTxn, SI!RunningTxnIds, RunIds
  <1>1. Ops(h') = Ops(h) \cup {aop} /\ h' \in Seq(Ops(h'))
    <2>1. h \in Seq(Ops(h))
      BY DEF TypeInv
    <2>2. Ops(Append(h, aop)) = Ops(h) \cup {aop} /\ Append(h, aop) \in Seq(Ops(h) \cup {aop})
      BY <2>1, RangeAppend
    <2> QED
      BY <2>2, <1>0
  <1>2. ~Aborted(h, tid) /\ ~Committed(h, tid) /\ Started(h, tid)
    BY <1>0, RunningFacts
  <1>3. UniqueOps(h')
    BY <1>1, <1>2 DEF HistInv, UniqueOps, Aborted
  <1>4. /\ \A t : Started(h', t) <=> Started(h, t)
        /\ \A t : Committed(h', t) <=> Committed(h, t)
        /\ \A t : Aborted(h', t) <=> (Aborted(h, t) \/ t = tid)
    BY <1>1, <1>2 DEF Started, Committed, Aborted
  <1>5. \A t : Started(h, t) => BT(h', t) = BT(h, t)
    <2> SUFFICES ASSUME NEW t, Started(h, t) PROVE BT(h', t) = BT(h, t)
      OBVIOUS
    <2>1. PICK b \in Ops(h) : b.txnId = t /\ b.type = "begin" /\ b.time = BT(h, t)
      BY StartedFacts
    <2> QED
      BY <2>1, <1>1, <1>3, ExtendTimes
  <1>6. \A t : Committed(h, t) => CT(h', t) = CT(h, t)
    <2> SUFFICES ASSUME NEW t, Committed(h, t) PROVE CT(h', t) = CT(h, t)
      OBVIOUS
    <2>1. PICK c \in Ops(h) : c.txnId = t /\ c.type = "commit"
      BY DEF Committed
    <2>2. CT(h, t) = c.time
      BY <2>1, CTVal DEF HistInv, UniqueOps
    <2> QED
      BY <2>1, <2>2, <1>1, <1>3, ExtendTimes
  <1>7. \A t : Started(h, t) => (Doomed(h', txnProg', t) <=> Doomed(h, txnProg, t))
    BY <1>0, <1>1, <1>5 DEF Doomed, KW
  <1>8. RunIds(runningTxns') = RunIds(runningTxns) \ {tid}
    BY <1>0 DEF RunIds
  <1>9. TypeInv'
    BY <1>0, <1>1 DEF TypeInv
  <1>10. HistInv'
    <2>1. \A op \in Ops(h') :
            /\ op.txnId \in TxnIds
            /\ op.type \in {"begin", "body", "commit", "abort"}
            /\ op.type = "body" => /\ op.reads  = txnProg'[op.txnId].reads
                                   /\ op.writes = txnProg'[op.txnId].writes
            /\ op.type \in {"begin", "commit", "abort"} => op.time \in Nat /\ op.time =< clock'
            /\ op.type = "commit" => /\ op.updatedKeys = KW(txnProg', op.txnId)
                                     /\ BT(h', op.txnId) < op.time
      <3> SUFFICES ASSUME NEW op \in Ops(h') PROVE
            /\ op.txnId \in TxnIds
            /\ op.type \in {"begin", "body", "commit", "abort"}
            /\ op.type = "body" => /\ op.reads  = txnProg'[op.txnId].reads
                                   /\ op.writes = txnProg'[op.txnId].writes
            /\ op.type \in {"begin", "commit", "abort"} => op.time \in Nat /\ op.time =< clock'
            /\ op.type = "commit" => /\ op.updatedKeys = KW(txnProg', op.txnId)
                                     /\ BT(h', op.txnId) < op.time
        OBVIOUS
      <3>1. CASE op = aop
        BY <3>1, <1>0 DEF TypeInv
      <3>2. CASE op \in Ops(h)
        <4>1. Started(h, op.txnId)
          BY <3>2 DEF Started
        <4> QED
          BY <3>2, <4>1, <1>0, <1>5 DEF HistInv, TypeInv, KW
      <3> QED
        BY <3>1, <3>2, <1>1
    <2>2. \A t \in TxnIds : Started(h', t) =>
            /\ \E op \in Ops(h') : op.txnId = t /\ op.type = "begin"
            /\ \E op \in Ops(h') : op.txnId = t /\ op.type = "body"
      BY <1>1, <1>4 DEF HistInv
    <2>3. \A r \in runningTxns' :
            /\ r.id \in TxnIds
            /\ Started(h', r.id)
            /\ r.startTime = BT(h', r.id)
            /\ ~Committed(h', r.id)
            /\ ~Aborted(h', r.id)
      BY <1>0, <1>4, <1>5 DEF HistInv
    <2> QED
      BY <2>1, <2>2, <2>3, <1>3 DEF HistInv, UniqueOps
  <1>11. SnapInv'
    BY <1>0, <1>4 DEF SnapInv, KW
  <1>12. DataInv'
    BY <1>0 DEF DataInv, DataInvS
  <1>13. BodyInv'
    <2> SUFFICES ASSUME NEW t \in TxnIds, Started(h', t)
                 PROVE  /\ Static(txnReq'[t], txnProg'[t])
                        /\ DelDyn(txnReq'[t], txnProg'[t], dataStore')
                        /\ txnReq'[t].type = "NewOrder" =>
                              \E o \in OIds :
                                  /\ NOStatic(txnReq'[t], txnProg'[t], o)
                                  /\ (t \in RunIds(runningTxns') /\ ~Doomed(h', txnProg', t)) =>
                                        dataStore'[NK(txnReq'[t].w, txnReq'[t].d)] = o
      BY DEF BodyInv
    <2>1. Started(h, t)
      BY <1>4
    <2> QED
      BY <2>1, <1>0, <1>7, <1>8 DEF BodyInv
  <1>14. SafeInv'
    <2>1. \A t1 \in RunIds(runningTxns') : Started(h, t1)
      BY <1>8, RunningFacts
    <2> QED
      BY <2>1, <1>0, <1>4, <1>5, <1>6, <1>7, <1>8 DEF SafeInv
  <1>15. RWInv'
    <2>1. \A t : Committed(h, t) => Started(h, t)
      BY DEF Committed, Started
    <2> QED
      BY <2>1, <1>0, <1>4, <1>5, <1>6 DEF RWInv
  <1> QED
    BY <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15

----------------------------------------------------------------------------
(***************************************************************************)
(* StartAndRun preserves the invariant.                                    *)
(***************************************************************************)

THEOREM StartStep ==
    ASSUME Inv, NEW tid \in TxnIds, NEW req \in Requests, StartAndRun(tid, req)
    PROVE  Inv'
  <1> DEFINE h == txnHistory
             P == txnProg
             B == ProgramFor(tid, req, dataStore)
             bop == [type |-> "begin", txnId |-> tid, time |-> clock + 1]
             bdy == [type |-> "body", txnId |-> tid, reads |-> B.reads, writes |-> B.writes]
             newTxn == [id |-> tid, startTime |-> clock + 1, commitTime |-> Empty]
  <1> USE DEF Inv
  <1>0. /\ ReqEnabled(req, dataStore)
        /\ ~Started(h, tid)
        /\ txnSnapshots' = [txnSnapshots EXCEPT ![tid] = SI!ApplyWrites(dataStore, B.writes)]
        /\ txnProg' = [txnProg EXCEPT ![tid] = B]
        /\ h' = h \o <<bop, bdy>>
        /\ runningTxns' = runningTxns \cup {newTxn}
        /\ clock' = clock + 1
        /\ dataStore' = dataStore
        /\ txnReq' = [txnReq EXCEPT ![tid] = req]
    BY DEF StartAndRun, SI!StartAndRun, Started, Ops
  <1>1. Ops(h') = Ops(h) \cup {bop, bdy} /\ h' \in Seq(Ops(h'))
    <2>1. h \in Seq(Ops(h))
      BY DEF TypeInv
    <2>2. Ops(h \o <<bop, bdy>>) = Ops(h) \cup {bop, bdy} /\ h \o <<bop, bdy>> \in Seq(Ops(h) \cup {bop, bdy})
      BY <2>1, RangeConcat2
    <2> QED
      BY <2>2, <1>0
  <1>b. \A op \in Ops(h) : op.txnId # tid
    BY <1>0 DEF Started
  <1>2. UniqueOps(h')
    <2> SUFFICES ASSUME NEW op1 \in Ops(h'), NEW op2 \in Ops(h'),
                        op1.txnId = op2.txnId, op1.type = op2.type
                 PROVE  op1 = op2
      BY DEF UniqueOps
    <2>1. CASE op1 \in Ops(h) /\ op2 \in Ops(h)
      BY <2>1 DEF HistInv
    <2>2. CASE op1 \in Ops(h) /\ op2 \notin Ops(h)
      BY <2>2, <1>b, <1>1
    <2>3. CASE op1 \notin Ops(h) /\ op2 \in Ops(h)
      BY <2>3, <1>b, <1>1
    <2>4. CASE op1 \notin Ops(h) /\ op2 \notin Ops(h)
      BY <2>4, <1>1
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4
  <1>3. /\ \A t : Started(h', t) <=> (Started(h, t) \/ t = tid)
        /\ \A t : Committed(h', t) <=> Committed(h, t)
        /\ \A t : Aborted(h', t) <=> Aborted(h, t)
    <2>1. \A t : Started(h', t) <=> (Started(h, t) \/ t = tid)
      BY <1>1 DEF Started
    <2>2. \A t : Committed(h', t) <=> Committed(h, t)
      BY <1>1 DEF Committed
    <2>3. \A t : Aborted(h', t) <=> Aborted(h, t)
      BY <1>1 DEF Aborted
    <2> QED
      BY <2>1, <2>2, <2>3
  <1>4. /\ \A t : Started(h, t) => BT(h', t) = BT(h, t)
        /\ BT(h', tid) = clock + 1
    <2>1. ASSUME NEW t, Started(h, t) PROVE BT(h', t) = BT(h, t)
      <3>1. PICK b \in Ops(h) : b.txnId = t /\ b.type = "begin" /\ b.time = BT(h, t)
        BY <2>1, StartedFacts
      <3> QED
        BY <3>1, <1>1, <1>2, ExtendTimes
    <2>2. BT(h', tid) = clock + 1
      <3>1. bop \in Ops(h') /\ bop.type = "begin" /\ bop.txnId = tid
        BY <1>1
      <3> QED
        BY <3>1, <1>2, BTVal
    <2> QED
      BY <2>1, <2>2
  <1>5. \A t : Committed(h, t) => CT(h', t) = CT(h, t)
    <2> SUFFICES ASSUME NEW t, Committed(h, t) PROVE CT(h', t) = CT(h, t)
      OBVIOUS
    <2>1. PICK c \in Ops(h) : c.txnId = t /\ c.type = "commit"
      BY DEF Committed
    <2>2. CT(h, t) = c.time
      BY <2>1, CTVal DEF HistInv, UniqueOps
    <2> QED
      BY <2>1, <2>2, <1>1, <1>2, ExtendTimes
  <1>6. /\ \A t \in TxnIds : t # tid => /\ txnProg'[t] = txnProg[t]
                                       /\ txnReq'[t] = txnReq[t]
                                       /\ txnSnapshots'[t] = txnSnapshots[t]
                                       /\ KW(txnProg', t) = KW(txnProg, t)
        /\ txnProg'[tid] = B /\ txnReq'[tid] = req
        /\ KW(txnProg', tid) = KWB(B)
    BY <1>0 DEF TypeInv, KW
  <1>a. \A t : Started(h, t) => t \in TxnIds /\ t # tid
    BY <1>0 DEF HistInv, Started
  <1>7. /\ \A t : Started(h, t) => (Doomed(h', txnProg', t) <=> Doomed(h, txnProg, t))
        /\ ~Doomed(h', txnProg', tid)
    <2>1. ASSUME NEW t, Started(h, t) PROVE Doomed(h', txnProg', t) <=> Doomed(h, txnProg, t)
      <3>1. KW(txnProg', t) = KW(txnProg, t) /\ BT(h', t) = BT(h, t)
        BY <2>1, <1>a, <1>6, <1>4
      <3>2. \A c \in Ops(h') : c.type = "commit" => c \in Ops(h)
        BY <1>1
      <3> QED
        BY <3>1, <3>2, <1>1 DEF Doomed
    <2>2. ~Doomed(h', txnProg', tid)
      <3> SUFFICES ASSUME NEW c \in Ops(h'), c.type = "commit", c.time > BT(h', tid)
                   PROVE  FALSE
        BY DEF Doomed
      <3>1. c \in Ops(h)
        BY <1>1
      <3>2. c.time \in Nat /\ c.time =< clock
        BY <3>1 DEF HistInv
      <3> QED
        BY <3>2, <1>4 DEF TypeInv
    <2> QED
      BY <2>1, <2>2
  <1>8. RunIds(runningTxns') = RunIds(runningTxns) \cup {tid} /\ tid \notin RunIds(runningTxns)
    <2>1. RunIds(runningTxns') = RunIds(runningTxns) \cup {tid}
      BY <1>0 DEF RunIds
    <2>2. tid \notin RunIds(runningTxns)
      BY <1>0, RunningFacts
    <2> QED
      BY <2>1, <2>2
  <1>9. /\ Static(req, B)
        /\ DelDyn(req, B, dataStore)
        /\ req.type = "NewOrder" =>
              /\ dataStore[NK(req.w, req.d)] \in OIds
              /\ NOStatic(req, B, dataStore[NK(req.w, req.d)])
    BY <1>0, ProgFor DEF DataInv
  <1>10. TypeInv'
    BY <1>0, <1>1 DEF TypeInv
  <1>11. HistInv'
    <2>1. \A op \in Ops(h') :
            /\ op.txnId \in TxnIds
            /\ op.type \in {"begin", "body", "commit", "abort"}
            /\ op.type = "body" => /\ op.reads  = txnProg'[op.txnId].reads
                                   /\ op.writes = txnProg'[op.txnId].writes
            /\ op.type \in {"begin", "commit", "abort"} => op.time \in Nat /\ op.time =< clock'
            /\ op.type = "commit" => /\ op.updatedKeys = KW(txnProg', op.txnId)
                                     /\ BT(h', op.txnId) < op.time
      <3> SUFFICES ASSUME NEW op \in Ops(h') PROVE
            /\ op.txnId \in TxnIds
            /\ op.type \in {"begin", "body", "commit", "abort"}
            /\ op.type = "body" => /\ op.reads  = txnProg'[op.txnId].reads
                                   /\ op.writes = txnProg'[op.txnId].writes
            /\ op.type \in {"begin", "commit", "abort"} => op.time \in Nat /\ op.time =< clock'
            /\ op.type = "commit" => /\ op.updatedKeys = KW(txnProg', op.txnId)
                                     /\ BT(h', op.txnId) < op.time
        OBVIOUS
      <3>1. CASE op = bop
        BY <3>1, <1>0 DEF TypeInv
      <3>2. CASE op = bdy
        BY <3>2, <1>6
      <3>3. CASE op \in Ops(h)
        <4>1. Started(h, op.txnId)
          BY <3>3 DEF Started
        <4>2. op.txnId # tid /\ op.txnId \in TxnIds
          BY <4>1, <1>a
        <4>3. op.type \in {"begin", "body", "commit", "abort"}
          BY <3>3 DEF HistInv
        <4>4. op.type = "body" => /\ op.reads  = txnProg'[op.txnId].reads
                                  /\ op.writes = txnProg'[op.txnId].writes
          BY <3>3, <4>2, <1>6 DEF HistInv
        <4>5. op.type \in {"begin", "commit", "abort"} => op.time \in Nat /\ op.time =< clock'
          BY <3>3, <1>0 DEF HistInv, TypeInv
        <4>6. op.type = "commit" => /\ op.updatedKeys = KW(txnProg', op.txnId)
                                    /\ BT(h', op.txnId) < op.time
          <5>1. BT(h', op.txnId) = BT(h, op.txnId)
            BY <4>1, <1>4
          <5> QED
            BY <3>3, <4>2, <5>1, <1>6 DEF HistInv
        <4> QED
          BY <4>2, <4>3, <4>4, <4>5, <4>6
      <3> QED
        BY <3>1, <3>2, <3>3, <1>1
    <2>2. \A t \in TxnIds : Started(h', t) =>
            /\ \E op \in Ops(h') : op.txnId = t /\ op.type = "begin"
            /\ \E op \in Ops(h') : op.txnId = t /\ op.type = "body"
      BY <1>1, <1>3 DEF HistInv
    <2>3. \A r \in runningTxns' :
            /\ r.id \in TxnIds
            /\ Started(h', r.id)
            /\ r.startTime = BT(h', r.id)
            /\ ~Committed(h', r.id)
            /\ ~Aborted(h', r.id)
      <3> SUFFICES ASSUME NEW r \in runningTxns' PROVE
            /\ r.id \in TxnIds
            /\ Started(h', r.id)
            /\ r.startTime = BT(h', r.id)
            /\ ~Committed(h', r.id)
            /\ ~Aborted(h', r.id)
        OBVIOUS
      <3>1. CASE r = newTxn
        <4>1. ~Committed(h, tid) /\ ~Aborted(h, tid)
          BY <1>0 DEF Started, Committed, Aborted
        <4> QED
          BY <3>1, <4>1, <1>3, <1>4
      <3>2. CASE r \in runningTxns
        BY <3>2, <1>3, <1>4 DEF HistInv
      <3> QED
        BY <3>1, <3>2, <1>0
    <2> QED
      BY <2>1, <2>2, <2>3, <1>2 DEF HistInv, UniqueOps
  <1>12. SnapInv'
    <2> SUFFICES ASSUME NEW t \in TxnIds, Started(h', t), NEW k \in KW(txnProg', t)
                 PROVE  txnSnapshots'[t][k] = WV(txnProg'[t], k)
      BY DEF SnapInv
    <2>1. CASE t = tid
      <3>1. k \in KWB(B) /\ k \in DOMAIN dataStore
        BY <2>1, <1>6 DEF KWB, TypeInv
      <3>2. txnSnapshots'[tid] = SI!ApplyWrites(dataStore, B.writes)
        BY <1>0 DEF TypeInv
      <3>3. SI!ApplyWrites(dataStore, B.writes)[k] = (CHOOSE wop \in B.writes : wop.key = k).val
        BY <3>1 DEF SI!ApplyWrites, KWB
      <3> QED
        BY <2>1, <3>2, <3>3, <1>6 DEF WV
    <2>2. CASE t # tid
      BY <2>2, <1>3, <1>6 DEF SnapInv
    <2> QED
      BY <2>1, <2>2
  <1>13. DataInv'
    BY <1>0 DEF DataInv, DataInvS
  <1>14. BodyInv'
    <2> SUFFICES ASSUME NEW t \in TxnIds, Started(h', t)
                 PROVE  /\ Static(txnReq'[t], txnProg'[t])
                        /\ DelDyn(txnReq'[t], txnProg'[t], dataStore')
                        /\ txnReq'[t].type = "NewOrder" =>
                              \E o \in OIds :
                                  /\ NOStatic(txnReq'[t], txnProg'[t], o)
                                  /\ (t \in RunIds(runningTxns') /\ ~Doomed(h', txnProg', t)) =>
                                        dataStore'[NK(txnReq'[t].w, txnReq'[t].d)] = o
      BY DEF BodyInv
    <2>1. CASE t = tid
      BY <2>1, <1>0, <1>6, <1>9
    <2>2. CASE t # tid
      <3>1. Started(h, t)
        BY <2>2, <1>3
      <3> QED
        BY <3>1, <2>2, <1>0, <1>6, <1>7, <1>8 DEF BodyInv
    <2> QED
      BY <2>1, <2>2
  <1>15. SafeInv'
    <2>1. \A t1 \in RunIds(runningTxns') : txnReq'[t1].type \in UpdTypes =>
             \A k \in RNWB(txnProg'[t1]) : \A y \in RunIds(runningTxns') :
                 (y # t1 /\ k \in KW(txnProg', y)) => Doomed(h', txnProg', y)
      <3> SUFFICES ASSUME NEW t1 \in RunIds(runningTxns'), txnReq'[t1].type \in UpdTypes,
                          NEW k \in RNWB(txnProg'[t1]), NEW y \in RunIds(runningTxns'),
                          y # t1, k \in KW(txnProg', y)
                   PROVE  Doomed(h', txnProg', y)
        OBVIOUS
      <3>1. CASE t1 # tid /\ y # tid
        <4>1. t1 \in RunIds(runningTxns) /\ y \in RunIds(runningTxns)
          BY <3>1, <1>8
        <4>2. Started(h, t1) /\ Started(h, y) /\ t1 \in TxnIds /\ y \in TxnIds
          BY <4>1, RunningFacts
        <4>3. Doomed(h, txnProg, y)
          BY <3>1, <4>1, <4>2, <1>6 DEF SafeInv
        <4> QED
          BY <4>2, <4>3, <1>7
      <3>2. CASE t1 # tid /\ y = tid
        <4>1. t1 \in RunIds(runningTxns)
          BY <3>2, <1>8
        <4>2. Started(h, t1) /\ t1 \in TxnIds
          BY <4>1, RunningFacts
        <4> DEFINE rq1 == txnReq[t1]
        <4>3. /\ Static(rq1, txnProg[t1])
              /\ DelDyn(rq1, txnProg[t1], dataStore)
              /\ k \in RNWB(txnProg[t1])
              /\ rq1.type \in UpdTypes
          BY <3>2, <4>2, <1>6 DEF BodyInv
        <4>4. PICK wop \in B.writes : wop.key = k
          BY <3>2, <1>6 DEF KWB
        <4>5. CASE rq1.type \in {"NewOrder", "Payment"}
          <5>1. k.col \in {"tax", "info"}
            BY <4>3, <4>5 DEF Static
          <5>2. wop.key.col \notin {"tax", "info"}
            BY <1>9 DEF Static
          <5> QED
            BY <4>4, <5>1, <5>2
        <4>6. CASE rq1.type = "Delivery"
          <5>1. /\ k.tbl \in {"ORDER", "ORDERLINE"} /\ k.col \in {"hdr", "items"}
                /\ k.w \in WIds /\ k.d \in DIds /\ k.o \in OIds
                /\ k.o < dataStore[NK(k.w, k.d)]
            BY <4>3, <4>6 DEF Static, DelDyn
          <5>2. CASE req.type = "NewOrder"
            <6>1. wop.key.w = req.w /\ wop.key.d = req.d /\ wop.key.o = dataStore[NK(req.w, req.d)]
              BY <5>1, <5>2, <4>4, <1>9 DEF NOStatic
            <6> QED
              BY <6>1, <5>1, <4>4
          <5>3. CASE req.type # "NewOrder"
            <6>1. ~(wop.key.tbl \in {"ORDER", "ORDERLINE"} /\ wop.key.col \in {"hdr", "items"})
              BY <5>3, <1>9 DEF Static
            <6> QED
              BY <6>1, <5>1, <4>4
          <5> QED
            BY <5>2, <5>3
        <4> QED
          BY <4>3, <4>5, <4>6 DEF UpdTypes
      <3>3. CASE t1 = tid /\ y # tid
        <4>1. y \in RunIds(runningTxns)
          BY <3>3, <1>8
        <4>2. Started(h, y) /\ y \in TxnIds
          BY <4>1, RunningFacts
        <4> DEFINE rqy == txnReq[y]
        <4>3. /\ Static(rqy, txnProg[y])
              /\ rqy.type = "NewOrder" =>
                    \E o \in OIds :
                        /\ NOStatic(rqy, txnProg[y], o)
                        /\ (y \in RunIds(runningTxns) /\ ~Doomed(h, txnProg, y)) =>
                              dataStore[NK(rqy.w, rqy.d)] = o
          BY <4>2 DEF BodyInv
        <4>4. k \in RNWB(B) /\ req.type \in UpdTypes
          BY <3>3, <1>6
        <4>5. PICK wop \in txnProg[y].writes : wop.key = k
          BY <3>3, <4>2, <1>6 DEF KW, KWB
        <4>6. CASE req.type \in {"NewOrder", "Payment"}
          <5>1. k.col \in {"tax", "info"}
            BY <4>4, <4>6, <1>9 DEF Static
          <5>2. wop.key.col \notin {"tax", "info"}
            BY <4>3 DEF Static
          <5> QED
            BY <4>5, <5>1, <5>2
        <4>7. CASE req.type = "Delivery"
          <5>1. /\ k.tbl \in {"ORDER", "ORDERLINE"} /\ k.col \in {"hdr", "items"}
                /\ k.w \in WIds /\ k.d \in DIds /\ k.o \in OIds
                /\ k.o < dataStore[NK(k.w, k.d)]
            BY <4>4, <4>7, <1>9 DEF Static, DelDyn
          <5>2. CASE rqy.type = "NewOrder"
            <6>1. PICK o \in OIds :
                     /\ NOStatic(rqy, txnProg[y], o)
                     /\ (y \in RunIds(runningTxns) /\ ~Doomed(h, txnProg, y)) =>
                           dataStore[NK(rqy.w, rqy.d)] = o
              BY <5>2, <4>3
            <6>2. wop.key.w = rqy.w /\ wop.key.d = rqy.d /\ wop.key.o = o
              BY <6>1, <5>1, <4>5 DEF NOStatic
            <6>3. Doomed(h, txnProg, y)
              BY <6>1, <6>2, <5>1, <4>1, <4>5
            <6> QED
              BY <6>3, <4>2, <1>7
          <5>3. CASE rqy.type # "NewOrder"
            <6>1. ~(wop.key.tbl \in {"ORDER", "ORDERLINE"} /\ wop.key.col \in {"hdr", "items"})
              BY <5>3, <4>3 DEF Static
            <6> QED
              BY <6>1, <5>1, <4>5
          <5> QED
            BY <5>2, <5>3
        <4> QED
          BY <4>4, <4>6, <4>7 DEF UpdTypes
      <3> QED
        BY <3>1, <3>2, <3>3
    <2>2. \A t1 \in RunIds(runningTxns') : txnReq'[t1].type \in UpdTypes =>
             \A k \in RNWB(txnProg'[t1]) : \A y \in TxnIds :
                 (Committed(h', y) /\ k \in KW(txnProg', y)) =>
                     CT(h', y) < BT(h', t1)
      <3> SUFFICES ASSUME NEW t1 \in RunIds(runningTxns'), txnReq'[t1].type \in UpdTypes,
                          NEW k \in RNWB(txnProg'[t1]), NEW y \in TxnIds,
                          Committed(h', y), k \in KW(txnProg', y)
                   PROVE  CT(h', y) < BT(h', t1)
        OBVIOUS
      <3>1. Committed(h, y) /\ Started(h, y) /\ y # tid
        BY <1>3, <1>a DEF Committed, Started
      <3>2. CT(h', y) = CT(h, y) /\ CT(h, y) \in Nat /\ CT(h, y) =< clock
        BY <3>1, <1>5, CommittedFacts
      <3>3. CASE t1 = tid
        BY <3>2, <3>3, <1>4 DEF TypeInv
      <3>4. CASE t1 # tid
        <4>1. t1 \in RunIds(runningTxns) /\ Started(h, t1) /\ t1 \in TxnIds
          BY <3>4, <1>8, RunningFacts
        <4>2. CT(h, y) < BT(h, t1)
          BY <3>1, <3>4, <4>1, <1>6 DEF SafeInv
        <4> QED
          BY <4>1, <4>2, <3>2, <1>4
      <3> QED
        BY <3>3, <3>4
    <2> QED
      BY <2>1, <2>2 DEF SafeInv
  <1>16. RWInv'
    <2> SUFFICES ASSUME NEW t1 \in TxnIds, NEW t2 \in TxnIds,
                        Committed(h', t1), Committed(h', t2), t1 # t2,
                        KW(txnProg', t1) # {},
                        \E k \in KW(txnProg', t2) : k \in txnProg'[t1].reads,
                        BT(h', t1) < CT(h', t2)
                 PROVE  CT(h', t1) < CT(h', t2)
      BY DEF RWInv
    <2>1. Committed(h, t1) /\ Committed(h, t2) /\ Started(h, t1) /\ Started(h, t2)
      BY <1>3 DEF Committed, Started
    <2>2. t1 # tid /\ t2 # tid
      BY <2>1, <1>a
    <2>3. /\ KW(txnProg', t1) = KW(txnProg, t1) /\ KW(txnProg', t2) = KW(txnProg, t2)
          /\ txnProg'[t1] = txnProg[t1]
      BY <2>2, <1>6
    <2>4. BT(h', t1) = BT(h, t1) /\ CT(h', t1) = CT(h, t1) /\ CT(h', t2) = CT(h, t2)
      BY <2>1, <1>4, <1>5
    <2> QED
      BY <2>1, <2>3, <2>4 DEF RWInv
  <1> QED
    BY <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16

----------------------------------------------------------------------------
(***************************************************************************)
(* CommitTxn preserves the invariant.                                      *)
(***************************************************************************)

THEOREM CommitStep ==
    ASSUME Inv, NEW tid \in TxnIds, CommitTxn(tid)
    PROVE  Inv'
  <1> DEFINE h == txnHistory
             P == txnProg
             KWT == KW(txnProg, tid)
             cop == [type |-> "commit", txnId |-> tid, time |-> clock + 1, updatedKeys |-> KWT]
             rq0 == txnReq[tid]
  <1> USE DEF Inv
  <1>a. /\ tid \in RunIds(runningTxns)
        /\ Started(h, tid) /\ ~Committed(h, tid) /\ ~Aborted(h, tid)
        /\ \E r \in runningTxns : r.id = tid /\ r.startTime = BT(h, tid)
        /\ BT(h, tid) \in Nat /\ BT(h, tid) =< clock
    <2>1. tid \in RunIds(runningTxns)
      BY DEF CommitTxn, SI!CommitTxn, SI!RunningTxnIds, RunIds
    <2> QED
      BY <2>1, RunningFacts, StartedFacts
  <1>b. SI!KeysWrittenByTxn(h, tid) = KWT
    <2>1. PICK bo \in Ops(h) : bo.txnId = tid /\ bo.type = "body"
      BY <1>a, StartedFacts
    <2>2. BodyMatch(h, txnProg)
      BY DEF HistInv, BodyMatch
    <2> QED
      BY <2>1, <2>2, HistKeys
  <1>0. /\ SI!TxnCanCommit(tid)
        /\ txnHistory' = Append(h, cop)
        /\ dataStore' = [k \in Keys |-> IF k \in KWT THEN WV(txnProg[tid], k) ELSE dataStore[k]]
        /\ runningTxns' = {r \in runningTxns : r.id # tid}
        /\ clock' = clock + 1
        /\ UNCHANGED <<txnSnapshots, txnProg, txnReq>>
    <2>1. \A k \in KWT : txnSnapshots[tid][k] = WV(txnProg[tid], k)
      BY <1>a DEF SnapInv
    <2> QED
      BY <1>b, <2>1 DEF CommitTxn, SI!CommitTxn
  <1>1. Ops(h') = Ops(h) \cup {cop} /\ h' \in Seq(Ops(h'))
    <2>1. h \in Seq(Ops(h))
      BY DEF TypeInv
    <2>2. Ops(Append(h, cop)) = Ops(h) \cup {cop} /\ Append(h, cop) \in Seq(Ops(h) \cup {cop})
      BY <2>1, RangeAppend
    <2> QED
      BY <2>2, <1>0
  <1>2. UniqueOps(h')
    <2> SUFFICES ASSUME NEW op1 \in Ops(h'), NEW op2 \in Ops(h'),
                        op1.txnId = op2.txnId, op1.type = op2.type
                 PROVE  op1 = op2
      BY DEF UniqueOps
    <2>1. CASE op1 \in Ops(h) /\ op2 \in Ops(h)
      BY <2>1 DEF HistInv
    <2>2. CASE op1 \in Ops(h) /\ op2 \notin Ops(h)
      BY <2>2, <1>a, <1>1 DEF Committed
    <2>3. CASE op1 \notin Ops(h) /\ op2 \in Ops(h)
      BY <2>3, <1>a, <1>1 DEF Committed
    <2>4. CASE op1 \notin Ops(h) /\ op2 \notin Ops(h)
      BY <2>4, <1>1
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4
  <1>3. /\ \A t : Started(h', t) <=> Started(h, t)
        /\ \A t : Committed(h', t) <=> (Committed(h, t) \/ t = tid)
        /\ \A t : Aborted(h', t) <=> Aborted(h, t)
    <2>1. \A t : Started(h', t) <=> Started(h, t)
      BY <1>1, <1>a DEF Started
    <2>2. \A t : Committed(h', t) <=> (Committed(h, t) \/ t = tid)
      BY <1>1 DEF Committed
    <2>3. \A t : Aborted(h', t) <=> Aborted(h, t)
      BY <1>1 DEF Aborted
    <2> QED
      BY <2>1, <2>2, <2>3
  <1>4. \A t : Started(h, t) => BT(h', t) = BT(h, t)
    <2> SUFFICES ASSUME NEW t, Started(h, t) PROVE BT(h', t) = BT(h, t)
      OBVIOUS
    <2>1. PICK b \in Ops(h) : b.txnId = t /\ b.type = "begin" /\ b.time = BT(h, t)
      BY StartedFacts
    <2> QED
      BY <2>1, <1>1, <1>2, ExtendTimes
  <1>5. /\ \A t : Committed(h, t) => CT(h', t) = CT(h, t)
        /\ CT(h', tid) = clock + 1
    <2>1. ASSUME NEW t, Committed(h, t) PROVE CT(h', t) = CT(h, t)
      <3>1. PICK c \in Ops(h) : c.txnId = t /\ c.type = "commit"
        BY <2>1 DEF Committed
      <3>2. CT(h, t) = c.time
        BY <3>1, CTVal DEF HistInv, UniqueOps
      <3> QED
        BY <3>1, <3>2, <1>1, <1>2, ExtendTimes
    <2>2. CT(h', tid) = clock + 1
      <3>1. cop \in Ops(h') /\ cop.type = "commit" /\ cop.txnId = tid
        BY <1>1
      <3> QED
        BY <3>1, <1>2, CTVal
    <2> QED
      BY <2>1, <2>2
  <1>6. ~Doomed(h, txnProg, tid)
    <2>1. PICK r \in runningTxns :
             /\ r.id = tid
             /\ ~\E op \in SI!Range(h) :
                   /\ op.type = "commit"
                   /\ op.time > r.startTime
                   /\ SI!KeysWrittenByTxn(h, tid) \cap op.updatedKeys # {}
      BY <1>0 DEF SI!TxnCanCommit
    <2>2. r.startTime = BT(h, tid)
      BY <2>1 DEF HistInv
    <2> QED
      BY <2>1, <2>2, <1>b DEF Doomed, KW, Ops
  <1>7. \A t : Started(h, t) =>
           /\ Doomed(h, txnProg, t) => Doomed(h', txnProg', t)
           /\ ~Doomed(h', txnProg', t) => (~Doomed(h, txnProg, t) /\ KW(txnProg, t) \cap KWT = {})
    <2> SUFFICES ASSUME NEW t, Started(h, t)
                 PROVE  /\ Doomed(h, txnProg, t) => Doomed(h', txnProg', t)
                        /\ ~Doomed(h', txnProg', t) => (~Doomed(h, txnProg, t) /\ KW(txnProg, t) \cap KWT = {})
      OBVIOUS
    <2>1. BT(h', t) = BT(h, t) /\ BT(h, t) \in Nat /\ BT(h, t) =< clock
      BY <1>4, StartedFacts
    <2>2. Doomed(h, txnProg, t) => Doomed(h', txnProg', t)
      BY <2>1, <1>0, <1>1 DEF Doomed
    <2>3. KW(txnProg, t) \cap KWT # {} => Doomed(h', txnProg', t)
      <3>1. cop \in Ops(h') /\ cop.time > BT(h', t)
        BY <2>1, <1>1 DEF TypeInv
      <3> QED
        BY <3>1, <1>0 DEF Doomed
    <2> QED
      BY <2>2, <2>3
  <1>8. RunIds(runningTxns') = RunIds(runningTxns) \ {tid}
    BY <1>0 DEF RunIds
  <1>9. /\ Static(rq0, txnProg[tid])
        /\ rq0.type = "NewOrder" =>
              \E o \in OIds :
                  /\ NOStatic(rq0, txnProg[tid], o)
                  /\ dataStore[NK(rq0.w, rq0.d)] = o
    BY <1>a, <1>6 DEF BodyInv
  <1>10. \A w \in WIds, d \in DIds :
            /\ dataStore'[NK(w, d)] \in Nat
            /\ dataStore[NK(w, d)] =< dataStore'[NK(w, d)]
            /\ NK(w, d) \notin KWT => dataStore'[NK(w, d)] = dataStore[NK(w, d)]
            /\ NK(w, d) \in KWT =>
                  /\ rq0.type = "NewOrder" /\ w = rq0.w /\ d = rq0.d
                  /\ dataStore'[NK(w, d)] = dataStore[NK(w, d)] + 1
    <2> SUFFICES ASSUME NEW w \in WIds, NEW d \in DIds
                 PROVE  /\ dataStore'[NK(w, d)] \in Nat
                        /\ dataStore[NK(w, d)] =< dataStore'[NK(w, d)]
                        /\ NK(w, d) \notin KWT => dataStore'[NK(w, d)] = dataStore[NK(w, d)]
                        /\ NK(w, d) \in KWT =>
                              /\ rq0.type = "NewOrder" /\ w = rq0.w /\ d = rq0.d
                              /\ dataStore'[NK(w, d)] = dataStore[NK(w, d)] + 1
      OBVIOUS
    <2>0. NK(w, d) \in Keys /\ dataStore[NK(w, d)] \in Nat
      BY NKInKeys DEF DataInv, DataInvS
    <2>1. dataStore'[NK(w, d)] = IF NK(w, d) \in KWT THEN WV(txnProg[tid], NK(w, d)) ELSE dataStore[NK(w, d)]
      BY <2>0, <1>0
    <2>2. CASE NK(w, d) \notin KWT
      BY <2>0, <2>1, <2>2
    <2>3. CASE NK(w, d) \in KWT
      <3>1. PICK wop \in txnProg[tid].writes : wop.key = NK(w, d)
        BY <2>3 DEF KW, KWB
      <3>2. rq0.type = "NewOrder"
        <4>1. wop.key.tbl = "DIST" /\ wop.key.col = "nextoid"
          BY <3>1, NKFields
        <4> QED
          BY <4>1, <1>9 DEF Static
      <3>3. PICK o \in OIds : NOStatic(rq0, txnProg[tid], o) /\ dataStore[NK(rq0.w, rq0.d)] = o
        BY <3>2, <1>9
      <3>4. w = rq0.w /\ d = rq0.d
        <4>1. NK(w, d) = NK(rq0.w, rq0.d)
          BY <3>1, <3>3, NKFields DEF NOStatic
        <4> QED
          BY <4>1, NKInj
      <3>5. WV(txnProg[tid], NK(w, d)) = o + 1
        <4> DEFINE c == CHOOSE x \in txnProg[tid].writes : x.key = NK(w, d)
        <4>1. c \in txnProg[tid].writes /\ c.key = NK(w, d)
          BY <3>1
        <4>2. c.val = o + 1
          BY <4>1, <3>3, NKFields DEF NOStatic
        <4> QED
          BY <4>2 DEF WV
      <3> QED
        BY <2>1, <2>3, <3>2, <3>3, <3>4, <3>5, <2>0
    <2> QED
      BY <2>2, <2>3
  <1>11. TypeInv'
    BY <1>0, <1>1 DEF TypeInv
  <1>12. HistInv'
    <2>1. \A op \in Ops(h') :
            /\ op.txnId \in TxnIds
            /\ op.type \in {"begin", "body", "commit", "abort"}
            /\ op.type = "body" => /\ op.reads  = txnProg'[op.txnId].reads
                                   /\ op.writes = txnProg'[op.txnId].writes
            /\ op.type \in {"begin", "commit", "abort"} => op.time \in Nat /\ op.time =< clock'
            /\ op.type = "commit" => /\ op.updatedKeys = KW(txnProg', op.txnId)
                                     /\ BT(h', op.txnId) < op.time
      <3> SUFFICES ASSUME NEW op \in Ops(h') PROVE
            /\ op.txnId \in TxnIds
            /\ op.type \in {"begin", "body", "commit", "abort"}
            /\ op.type = "body" => /\ op.reads  = txnProg'[op.txnId].reads
                                   /\ op.writes = txnProg'[op.txnId].writes
            /\ op.type \in {"begin", "commit", "abort"} => op.time \in Nat /\ op.time =< clock'
            /\ op.type = "commit" => /\ op.updatedKeys = KW(txnProg', op.txnId)
                                     /\ BT(h', op.txnId) < op.time
        OBVIOUS
      <3>1. CASE op = cop
        <4>1. BT(h', tid) = BT(h, tid)
          BY <1>a, <1>4
        <4>2. op.txnId = tid /\ op.type = "commit" /\ op.time = clock + 1 /\ op.updatedKeys = KWT
          BY <3>1
        <4>3. clock \in Nat /\ clock' = clock + 1 /\ txnProg' = txnProg
          BY <1>0 DEF TypeInv
        <4>4. op.time \in Nat /\ op.time =< clock' /\ BT(h', op.txnId) < op.time
          BY <4>1, <4>2, <4>3, <1>a
        <4>5. op.updatedKeys = KW(txnProg', op.txnId)
          BY <4>2, <4>3
        <4> QED
          BY <4>2, <4>4, <4>5
      <3>2. CASE op \in Ops(h)
        <4>1. Started(h, op.txnId)
          BY <3>2 DEF Started
        <4>2. op.type \in {"begin", "commit", "abort"} => op.time \in Nat /\ op.time =< clock'
          BY <3>2, <1>0 DEF HistInv, TypeInv
        <4>3. op.type = "commit" => BT(h', op.txnId) < op.time
          BY <3>2, <4>1, <1>4 DEF HistInv
        <4> QED
          BY <3>2, <4>2, <4>3, <1>0 DEF HistInv
      <3> QED
        BY <3>1, <3>2, <1>1
    <2>2. \A t \in TxnIds : Started(h', t) =>
            /\ \E op \in Ops(h') : op.txnId = t /\ op.type = "begin"
            /\ \E op \in Ops(h') : op.txnId = t /\ op.type = "body"
      BY <1>1, <1>3 DEF HistInv
    <2>3. \A r \in runningTxns' :
            /\ r.id \in TxnIds
            /\ Started(h', r.id)
            /\ r.startTime = BT(h', r.id)
            /\ ~Committed(h', r.id)
            /\ ~Aborted(h', r.id)
      BY <1>0, <1>3, <1>4 DEF HistInv
    <2> QED
      BY <2>1, <2>2, <2>3, <1>2 DEF HistInv, UniqueOps
  <1>13. SnapInv'
    BY <1>0, <1>3 DEF SnapInv
  <1>14. DataInv'
    <2>1. \A w \in WIds, d \in DIds : dataStore'[NK(w, d)] \in Nat
      BY <1>10
    <2>2. ASSUME NEW w \in WIds, NEW d \in DIds, NEW o \in OIds,
                 dataStore'[NOK(w, d, o)] # Empty
          PROVE  o < dataStore'[NK(w, d)]
      <3>0. NOK(w, d, o) \in Keys /\ dataStore[NK(w, d)] \in Nat /\ o \in Nat
        BY NOKInKeys DEF DataInv, DataInvS, OIds
      <3>1. dataStore'[NOK(w, d, o)] = IF NOK(w, d, o) \in KWT THEN WV(txnProg[tid], NOK(w, d, o)) ELSE dataStore[NOK(w, d, o)]
        BY <3>0, <1>0
      <3>2. CASE NOK(w, d, o) \notin KWT
        <4>1. o < dataStore[NK(w, d)]
          BY <3>1, <3>2, <2>2 DEF DataInv, DataInvS
        <4> QED
          BY <4>1, <3>0, <1>10
      <3>3. CASE NOK(w, d, o) \in KWT
        <4> DEFINE c == CHOOSE x \in txnProg[tid].writes : x.key = NOK(w, d, o)
        <4>1. c \in txnProg[tid].writes /\ c.key = NOK(w, d, o)
          BY <3>3 DEF KW, KWB
        <4>2. dataStore'[NOK(w, d, o)] = c.val
          BY <3>1, <3>3 DEF WV
        <4>3. c.key.tbl = "NEWORDER" /\ c.key.w = w /\ c.key.d = d /\ c.key.o = o
          BY <4>1, NOKFields
        <4>4. rq0.type = "NewOrder"
          <5> SUFFICES ASSUME rq0.type # "NewOrder" PROVE FALSE
            OBVIOUS
          <5>1. \A x \in txnProg[tid].writes : x.key.tbl = "NEWORDER" => x.val = Empty
            BY <1>9 DEF Static
          <5> QED
            BY <5>1, <4>1, <4>2, <4>3, <2>2
        <4>5. PICK oo \in OIds : NOStatic(rq0, txnProg[tid], oo) /\ dataStore[NK(rq0.w, rq0.d)] = oo
          BY <4>4, <1>9
        <4>6. w = rq0.w /\ d = rq0.d /\ o = oo
          BY <4>1, <4>3, <4>5 DEF NOStatic
        <4>7. NK(w, d) \in KWT
          BY <4>5, <4>6 DEF NOStatic, KW
        <4>8. dataStore'[NK(w, d)] = oo + 1
          BY <4>5, <4>6, <4>7, <1>10
        <4> QED
          BY <4>6, <4>8, <3>0
      <3> QED
        BY <3>2, <3>3
    <2> QED
      BY <2>1, <2>2 DEF DataInv, DataInvS
  <1>15. BodyInv'
    <2> SUFFICES ASSUME NEW t \in TxnIds, Started(h', t)
                 PROVE  /\ Static(txnReq'[t], txnProg'[t])
                        /\ DelDyn(txnReq'[t], txnProg'[t], dataStore')
                        /\ txnReq'[t].type = "NewOrder" =>
                              \E o \in OIds :
                                  /\ NOStatic(txnReq'[t], txnProg'[t], o)
                                  /\ (t \in RunIds(runningTxns') /\ ~Doomed(h', txnProg', t)) =>
                                        dataStore'[NK(txnReq'[t].w, txnReq'[t].d)] = o
      BY DEF BodyInv
    <2>1. Started(h, t)
      BY <1>3
    <2> DEFINE rq == txnReq[t]
    <2>2. /\ Static(rq, txnProg[t])
          /\ DelDyn(rq, txnProg[t], dataStore)
          /\ rq.type = "NewOrder" =>
                \E o \in OIds :
                    /\ NOStatic(rq, txnProg[t], o)
                    /\ (t \in RunIds(runningTxns) /\ ~Doomed(h, txnProg, t)) =>
                          dataStore[NK(rq.w, rq.d)] = o
      BY <2>1 DEF BodyInv
    <2>3. DelDyn(rq, txnProg[t], dataStore')
      <3> SUFFICES ASSUME rq.type = "Delivery", NEW k \in RNWB(txnProg[t])
                   PROVE  k.o < dataStore'[NK(k.w, k.d)]
        BY DEF DelDyn
      <3>1. k.w \in WIds /\ k.d \in DIds /\ k.o \in OIds /\ k.o < dataStore[NK(k.w, k.d)]
        BY <2>2 DEF Static, DelDyn
      <3>2. dataStore[NK(k.w, k.d)] \in Nat /\ dataStore'[NK(k.w, k.d)] \in Nat
            /\ dataStore[NK(k.w, k.d)] =< dataStore'[NK(k.w, k.d)]
        BY <3>1, <1>10 DEF DataInv, DataInvS
      <3> QED
        BY <3>1, <3>2 DEF OIds
    <2>4. rq.type = "NewOrder" =>
             \E o \in OIds :
                 /\ NOStatic(rq, txnProg[t], o)
                 /\ (t \in RunIds(runningTxns') /\ ~Doomed(h', txnProg', t)) =>
                       dataStore'[NK(rq.w, rq.d)] = o
      <3> SUFFICES ASSUME rq.type = "NewOrder"
                   PROVE  \E o \in OIds :
                             /\ NOStatic(rq, txnProg[t], o)
                             /\ (t \in RunIds(runningTxns') /\ ~Doomed(h', txnProg', t)) =>
                                   dataStore'[NK(rq.w, rq.d)] = o
        OBVIOUS
      <3>1. PICK o \in OIds :
               /\ NOStatic(rq, txnProg[t], o)
               /\ (t \in RunIds(runningTxns) /\ ~Doomed(h, txnProg, t)) =>
                     dataStore[NK(rq.w, rq.d)] = o
        BY <2>2
      <3>2. ASSUME t \in RunIds(runningTxns'), ~Doomed(h', txnProg', t)
            PROVE  dataStore'[NK(rq.w, rq.d)] = o
        <4>1. t \in RunIds(runningTxns) /\ ~Doomed(h, txnProg, t) /\ KW(txnProg, t) \cap KWT = {}
          BY <3>2, <2>1, <1>7, <1>8
        <4>2. NK(rq.w, rq.d) \in KW(txnProg, t)
          BY <3>1 DEF NOStatic, KW
        <4>3. rq.w \in WIds /\ rq.d \in DIds
          BY <2>2, ReqTypes DEF Static
        <4> QED
          BY <4>1, <4>2, <4>3, <3>1, <1>10
      <3> QED
        BY <3>1, <3>2
    <2> QED
      BY <2>2, <2>3, <2>4, <1>0
  <1>16. SafeInv'
    <2>1. \A t1 \in RunIds(runningTxns') : txnReq'[t1].type \in UpdTypes =>
             \A k \in RNWB(txnProg'[t1]) : \A y \in RunIds(runningTxns') :
                 (y # t1 /\ k \in KW(txnProg', y)) => Doomed(h', txnProg', y)
      <3> SUFFICES ASSUME NEW t1 \in RunIds(runningTxns'), txnReq'[t1].type \in UpdTypes,
                          NEW k \in RNWB(txnProg'[t1]), NEW y \in RunIds(runningTxns'),
                          y # t1, k \in KW(txnProg', y)
                   PROVE  Doomed(h', txnProg', y)
        OBVIOUS
      <3>1. t1 \in RunIds(runningTxns) /\ y \in RunIds(runningTxns)
        BY <1>8
      <3>2. Doomed(h, txnProg, y) /\ Started(h, y)
        BY <3>1, <1>0, RunningFacts DEF SafeInv
      <3> QED
        BY <3>2, <1>7
    <2>2. \A t1 \in RunIds(runningTxns') : txnReq'[t1].type \in UpdTypes =>
             \A k \in RNWB(txnProg'[t1]) : \A y \in TxnIds :
                 (Committed(h', y) /\ k \in KW(txnProg', y)) =>
                     CT(h', y) < BT(h', t1)
      <3> SUFFICES ASSUME NEW t1 \in RunIds(runningTxns'), txnReq'[t1].type \in UpdTypes,
                          NEW k \in RNWB(txnProg'[t1]), NEW y \in TxnIds,
                          Committed(h', y), k \in KW(txnProg', y)
                   PROVE  CT(h', y) < BT(h', t1)
        OBVIOUS
      <3>1. t1 \in RunIds(runningTxns) /\ t1 # tid /\ Started(h, t1)
        BY <1>8, RunningFacts
      <3>2. CASE y = tid
        <4>1. Doomed(h, txnProg, tid)
          BY <3>1, <3>2, <1>a, <1>0 DEF SafeInv
        <4> QED
          BY <4>1, <1>6
      <3>3. CASE y # tid
        <4>1. Committed(h, y)
          BY <3>3, <1>3
        <4>2. CT(h, y) < BT(h, t1)
          BY <4>1, <3>1, <1>0 DEF SafeInv
        <4> QED
          BY <4>1, <4>2, <3>1, <1>4, <1>5
      <3> QED
        BY <3>2, <3>3
    <2> QED
      BY <2>1, <2>2 DEF SafeInv
  <1>17. RWInv'
    <2> SUFFICES ASSUME NEW t1 \in TxnIds, NEW t2 \in TxnIds,
                        Committed(h', t1), Committed(h', t2), t1 # t2,
                        KW(txnProg', t1) # {},
                        \E k \in KW(txnProg', t2) : k \in txnProg'[t1].reads,
                        BT(h', t1) < CT(h', t2)
                 PROVE  CT(h', t1) < CT(h', t2)
      BY DEF RWInv
    <2>1. CASE t1 # tid /\ t2 # tid
      <3>1. Committed(h, t1) /\ Committed(h, t2) /\ Started(h, t1)
        BY <2>1, <1>3 DEF Committed, Started
      <3>2. BT(h', t1) = BT(h, t1) /\ CT(h', t1) = CT(h, t1) /\ CT(h', t2) = CT(h, t2)
        BY <3>1, <1>4, <1>5
      <3> QED
        BY <3>1, <3>2, <1>0 DEF RWInv
    <2>2. CASE t2 = tid
      <3>1. Committed(h, t1)
        BY <2>2, <1>3
      <3>2. CT(h', t1) = CT(h, t1) /\ CT(h, t1) \in Nat /\ CT(h, t1) =< clock
        BY <3>1, <1>5, CommittedFacts
      <3> QED
        BY <2>2, <3>2, <1>5 DEF TypeInv
    <2>3. CASE t1 = tid
      <3>1. Committed(h, t2) /\ t2 # tid
        BY <2>3, <1>3
      <3>2. PICK c2 \in Ops(h) : c2.txnId = t2 /\ c2.type = "commit"
        BY <3>1 DEF Committed
      <3>3. CT(h, t2) = c2.time /\ c2.updatedKeys = KW(txnProg, t2)
        BY <3>2, CTVal DEF HistInv, UniqueOps
      <3>4. BT(h, tid) < c2.time
        BY <2>3, <3>1, <3>3, <1>a, <1>4, <1>5
      <3>5. PICK k \in KW(txnProg, t2) : k \in txnProg[tid].reads
        BY <2>3, <1>0
      <3>6. CASE k \in KWT
        <4>1. Doomed(h, txnProg, tid)
          BY <3>2, <3>3, <3>4, <3>5, <3>6 DEF Doomed
        <4> QED
          BY <4>1, <1>6
      <3>7. CASE k \notin KWT
        <4>1. k \in RNWB(txnProg[tid])
          BY <3>5, <3>7 DEF RNWB, KW, KWB
        <4>2. rq0.type \in UpdTypes
          <5>1. txnProg[tid].writes # {}
            BY <2>3, <1>0 DEF KW, KWB
          <5> QED
            BY <5>1, <1>9 DEF Static
        <4>3. CT(h, t2) < BT(h, tid)
          BY <4>1, <4>2, <3>1, <3>5, <1>a DEF SafeInv
        <4>4. c2.time \in Nat
          BY <3>2 DEF HistInv
        <4> QED
          BY <4>3, <4>4, <3>3, <3>4, <1>a
      <3> QED
        BY <3>6, <3>7
    <2> QED
      BY <2>1, <2>2, <2>3
  <1> QED
    BY <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17

----------------------------------------------------------------------------
(***************************************************************************)
(* The main theorem.                                                       *)
(***************************************************************************)

THEOREM NextInv ==
    Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <1>1. ASSUME NEW tid \in TxnIds, NEW req \in Requests, StartAndRun(tid, req) PROVE Inv'
    BY <1>1, StartStep
  <1>2. ASSUME NEW tid \in TxnIds, CommitTxn(tid) PROVE Inv'
    BY <1>2, CommitStep
  <1>3. ASSUME NEW tid \in TxnIds, AbortTxn(tid) PROVE Inv'
    BY <1>3, AbortStep
  <1>4. ASSUME UNCHANGED vars PROVE Inv'
    BY <1>4 DEF vars, Inv, TypeInv, HistInv, SnapInv, DataInv, DataInvS, BodyInv, SafeInv, RWInv,
                Ops, Started, Committed, Aborted, BT, CT, KW, Doomed, RunIds
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4 DEF Next

THEOREM Safety ==
    Spec => []SerializableViaPath
  <1>1. Init => Inv
    BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'
    BY NextInv
  <1>3. Inv => SerializableViaPath
    BY InvSerializable
  <1> QED
    BY <1>1, <1>2, <1>3, PTL DEF Spec

=============================================================================
