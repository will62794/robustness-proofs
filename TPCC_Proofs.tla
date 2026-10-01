------------------------------ MODULE TPCC_Proofs ------------------------------
(**************************************************************************************************)
(*                                                                                                *)
(* A TLAPS proof of  Spec => []SerializableViaPath  for TPCC.tla.                                 *)
(*                                                                                                *)
(**************************************************************************************************)
EXTENDS TPCC, TLAPS, SequenceTheorems, NaturalsInduction

(**************************************************************************************************)
(* Part 0.  Standing assumptions.                                                                 *)
(**************************************************************************************************)

ASSUME ColGran == ColumnGranularity = TRUE

ASSUME RobustMix ==
    EnabledTxnTypes \subseteq {"NewOrder", "Payment", "OrderStatus", "StockLevel"}

----------------------------------------------------------------------------------------------------
(**************************************************************************************************)
(* Part 1.  The base case: the empty history is serializable.                                     *)
(**************************************************************************************************)

LEMMA EmptyRange == Range(<<>>) = {}
  BY DEF Range

LEMMA EmptyCommitted == CommittedTxns(<<>>) = {}
  BY EmptyRange DEF CommittedTxns

LEMMA EmptyGraph == SerializationGraph(<<>>) = {}
  BY EmptyCommitted DEF SerializationGraph

LEMMA EmptyPaths == Paths({}) = {}
  BY DEF Paths, GraphNodes

LEMMA EmptyNoCycle == IsCycleViaPath({}) = FALSE
  BY EmptyPaths DEF IsCycleViaPath

THEOREM Base == Init => SerializableViaPath
PROOF
  <1>1. Init => txnHistory = <<>> BY DEF Init
  <1>2. Init => SerializationGraph(txnHistory) = {} BY <1>1, EmptyGraph
  <1>3. QED
    BY <1>2, EmptyNoCycle DEF SerializableViaPath, IsConflictSerializableViaPath

----------------------------------------------------------------------------------------------------
(**************************************************************************************************)
(* Part 2.  A graph carrying a strictly increasing integer rank has no cycle.                     *)
(*                                                                                                *)
(* This is the only place `Paths` is reasoned about.  A path is an element of `[1..n -> nodes]`,  *)
(* so induction on the index gives `Rank(p[1]) < Rank(p[j])` for every j > 1; a cycle would make  *)
(* j = Len(p) give `Rank(p[1]) < Rank(p[1])`.                                                     *)
(**************************************************************************************************)

LEMMA PathShape ==
  ASSUME NEW edges, NEW p \in Paths(edges)
  PROVE  /\ p \in Seq(GraphNodes(edges))
         /\ DOMAIN p = 1..Len(p)
         /\ \A i \in 1..(Len(p)-1) : <<p[i], p[i+1]>> \in edges
PROOF
  <1> DEFINE nodes == GraphNodes(edges)
             maxLen == Cardinality(nodes) + 1
  <1>1. p \in UNION {[1..n -> nodes] : n \in 1..maxLen}
    BY DEF Paths
  <1>2. PICK n \in 1..maxLen : p \in [1..n -> nodes]
    BY <1>1
  <1>3. p \in Seq(nodes)
    BY <1>2 DEF Seq
  <1>4. DOMAIN p = 1..Len(p) BY <1>3, LenProperties
  <1>5. \A i \in 1..(Len(p)-1) : <<p[i], p[i+1]>> \in edges
    BY DEF Paths
  <1>6. QED BY <1>3, <1>4, <1>5

LEMMA NoCycleByRank ==
  ASSUME NEW edges, NEW Rank(_),
         \A x \in GraphNodes(edges) : Rank(x) \in Nat,
         \A e \in edges : Rank(e[1]) < Rank(e[2])
  PROVE  ~IsCycleViaPath(edges)
PROOF
  <1> SUFFICES ASSUME IsCycleViaPath(edges) PROVE FALSE OBVIOUS
  <1>1. PICK p \in Paths(edges) : Len(p) > 1 /\ p[1] = p[Len(p)]
    BY DEF IsCycleViaPath
  <1> DEFINE nodes == GraphNodes(edges)
             n == Len(p)
  <1>2. /\ p \in Seq(nodes)
        /\ DOMAIN p = 1..n
        /\ \A i \in 1..(n-1) : <<p[i], p[i+1]>> \in edges
    BY <1>1, PathShape
  <1>3. n \in Nat BY <1>2, LenProperties
  <1>4. \A i \in 1..n : p[i] \in nodes
    BY <1>2 DEF Seq
  <1>5. \A i \in 1..(n-1) : Rank(p[i]) < Rank(p[i+1])
    BY <1>2
  \* The induction.
  <1> DEFINE P(j) == (j \in 2..n) => Rank(p[1]) < Rank(p[j])
  <1>6. P(0) BY <1>3
  <1>7. \A j \in Nat : P(j) => P(j+1)
    <2>1. SUFFICES ASSUME NEW j \in Nat, P(j), (j+1) \in 2..n
                   PROVE  Rank(p[1]) < Rank(p[j+1])
      OBVIOUS
    <2>2. j \in 1..(n-1) BY <2>1, <1>3
    <2>3. Rank(p[j]) < Rank(p[j+1]) BY <2>2, <1>5
    <2>4. CASE j = 1
      BY <2>3, <2>4
    <2>5. CASE j # 1
      <3>1. j \in 2..n BY <2>1, <2>2, <2>5, <1>3
      <3>2. Rank(p[1]) < Rank(p[j]) BY <3>1, <2>1
      <3>3. /\ Rank(p[1]) \in Nat
            /\ Rank(p[j]) \in Nat
            /\ Rank(p[j+1]) \in Nat
        BY <1>4, <3>1, <2>2, <1>3
      <3>4. QED BY <3>2, <2>3, <3>3
    <2>6. QED BY <2>4, <2>5
  <1>8. \A j \in Nat : P(j) BY <1>6, <1>7, NatInduction, Isa
  <1>9. n \in 2..n BY <1>1, <1>3
  <1>10. Rank(p[1]) < Rank(p[n]) BY <1>8, <1>9, <1>3
  <1>11. QED BY <1>10, <1>1, <1>4, <1>3

----------------------------------------------------------------------------------------------------
(**************************************************************************************************)
(* Part 3.  The history properties, and the fact that they make every edge increase the rank.     *)
(*                                                                                                *)
(* Four facts about a history suffice.  Writing bg/cm for begin and commit times:                 *)
(*                                                                                                *)
(*   H1  bg(t) < cm(t)                              -- the clock ticks on both events             *)
(*   H2  a committed transaction never writes a read-only column group  -- THE WORKLOAD           *)
(*   H3  an updater reads a writable key only if it also writes it      -- THE WORKLOAD           *)
(*   H4  two committed transactions writing a common key have disjoint lifetimes  -- FCW          *)
(*                                                                                                *)
(* `ReadOnlyKey` names the four column groups no TPC-C statement writes: W_TAX, D_TAX,            *)
(* CUSTOMER.info and the whole ITEM table.  New-Order reads all four without writing them, which  *)
(* is why H3 has to be relativised; under row granularity W_TAX collapses into the WAREHOUSE row  *)
(* that Payment writes, `ReadOnlyKey` becomes empty of warehouse keys, and H3 genuinely fails.    *)
(**************************************************************************************************)

ReadOnlyKey(k) ==
    \/ k.tbl \in {"WH", "DIST"} /\ k.col = "tax"
    \/ k.tbl = "CUST" /\ k.col = "info"
    \/ k.tbl = "ITEM"

Updater(h, t) == \E k \in Keys : WritesKey(h, t, k)

Rank(h, t) == IF Updater(h, t) THEN CommitOp(h, t).time ELSE BeginOp(h, t).time

HistoryOK(h) ==
    \A t1, t2 \in CommittedTxns(h) :
        /\ BeginOp(h, t1).time \in Nat
        /\ CommitOp(h, t1).time \in Nat
        \* H1
        /\ BeginOp(h, t1).time < CommitOp(h, t1).time
        \* H2
        /\ \A k \in Keys : WritesKey(h, t1, k) => ~ReadOnlyKey(k)
        \* H3
        /\ Updater(h, t1) =>
             \A k \in Keys : ReadsKey(h, t1, k) =>
                 (WritesKey(h, t1, k) \/ ReadOnlyKey(k))
        \* H4
        /\ (t1 # t2 /\ (\E k \in Keys : WritesKey(h, t1, k) /\ WritesKey(h, t2, k)))
             => \/ CommitOp(h, t1).time =< BeginOp(h, t2).time
                \/ CommitOp(h, t2).time =< BeginOp(h, t1).time

\* The graph's nodes are committed transactions.
LEMMA NodesAreCommitted ==
  ASSUME NEW h
  PROVE  GraphNodes(SerializationGraph(h)) \subseteq CommittedTxns(h)
PROOF
  <1>1. SerializationGraph(h) \subseteq CommittedTxns(h) \X CommittedTxns(h)
    BY DEF SerializationGraph
  <1>2. QED BY <1>1 DEF GraphNodes

LEMMA EdgeIncreasesRank ==
  ASSUME NEW h, HistoryOK(h), NEW e \in SerializationGraph(h)
  PROVE  Rank(h, e[1]) < Rank(h, e[2])
PROOF
  <1> DEFINE CT == CommittedTxns(h)
             t1 == e[1]
             t2 == e[2]
             bg(t) == BeginOp(h, t).time
             cm(t) == CommitOp(h, t).time
  <1>1. /\ t1 \in CT /\ t2 \in CT
        /\ t1 # t2
        /\ \/ WWDependency(h, t1, t2)
           \/ WRDependency(h, t1, t2)
           \/ RWDependency(h, t1, t2)
    BY DEF SerializationGraph
  <1>2. \A t \in CT : bg(t) \in Nat /\ cm(t) \in Nat /\ bg(t) < cm(t)
    BY <1>1 DEF HistoryOK
  <1>3. /\ bg(t1) \in Nat /\ cm(t1) \in Nat /\ bg(t1) < cm(t1)
        /\ bg(t2) \in Nat /\ cm(t2) \in Nat /\ bg(t2) < cm(t2)
    BY <1>1, <1>2
  \* In every case t2 turns out to be an updater or the edge bounds cm(t2) from above;
  \* the four cases are handled separately.
  <1>4. CASE WWDependency(h, t1, t2)
    <2>1. cm(t1) < cm(t2) BY <1>4 DEF WWDependency
    <2>2. Updater(h, t1) /\ Updater(h, t2) BY <1>4 DEF WWDependency, Updater
    <2>3. Rank(h, t1) = cm(t1) /\ Rank(h, t2) = cm(t2) BY <2>2 DEF Rank
    <2>4. QED BY <2>1, <2>3
  <1>5. CASE WRDependency(h, t1, t2)
    <2>1. cm(t1) < bg(t2) BY <1>5 DEF WRDependency
    <2>2. Updater(h, t1) BY <1>5 DEF WRDependency, Updater
    <2>3. Rank(h, t1) = cm(t1) BY <2>2 DEF Rank
    <2>4. Rank(h, t2) = bg(t2) \/ Rank(h, t2) = cm(t2) BY DEF Rank
    <2>5. bg(t2) =< Rank(h, t2) BY <2>4, <1>3
    <2>6. QED BY <2>1, <2>3, <2>5, <1>3, <2>4
  <1>6. CASE RWDependency(h, t1, t2) /\ ~Updater(h, t1)
    <2>1. bg(t1) < cm(t2) BY <1>6 DEF RWDependency
    <2>2. Rank(h, t1) = bg(t1) BY <1>6 DEF Rank
    <2>3. Updater(h, t2) BY <1>6 DEF RWDependency, Updater
    <2>4. Rank(h, t2) = cm(t2) BY <2>3 DEF Rank
    <2>5. QED BY <2>1, <2>2, <2>4
  <1>7. CASE RWDependency(h, t1, t2) /\ Updater(h, t1)
    \* The interesting case: First-Committer-Wins has already ordered the pair.
    <2>1. PICK k \in Keys : ReadsKey(h, t1, k) /\ WritesKey(h, t2, k)
      BY <1>7 DEF RWDependency
    <2>2. bg(t1) < cm(t2) BY <1>7 DEF RWDependency
    <2>3. ~ReadOnlyKey(k) BY <1>1, <2>1 DEF HistoryOK
    <2>4. WritesKey(h, t1, k) BY <1>1, <1>7, <2>1, <2>3 DEF HistoryOK
    <2>5. cm(t1) =< bg(t2) \/ cm(t2) =< bg(t1)
      BY <1>1, <2>1, <2>4 DEF HistoryOK
    <2>6. cm(t1) =< bg(t2) BY <2>5, <2>2, <1>3
    <2>7. Updater(h, t2) BY <2>1 DEF Updater
    <2>8. Rank(h, t1) = cm(t1) /\ Rank(h, t2) = cm(t2) BY <1>7, <2>7 DEF Rank
    <2>9. QED BY <2>6, <2>8, <1>3
  <1>8. QED BY <1>1, <1>4, <1>5, <1>6, <1>7

THEOREM HistoryOKImpliesSerializable ==
  ASSUME NEW h, HistoryOK(h)
  PROVE  IsConflictSerializableViaPath(h)
PROOF
  <1> DEFINE edges == SerializationGraph(h)
             Rk(t) == Rank(h, t)
  <1>1. \A x \in GraphNodes(edges) : Rk(x) \in Nat
    <2>1. SUFFICES ASSUME NEW x \in GraphNodes(edges) PROVE Rk(x) \in Nat OBVIOUS
    <2>2. x \in CommittedTxns(h) BY NodesAreCommitted
    <2>3. BeginOp(h, x).time \in Nat /\ CommitOp(h, x).time \in Nat
      BY <2>2 DEF HistoryOK
    <2>4. QED BY <2>3 DEF Rank
  <1>2. \A e \in edges : Rk(e[1]) < Rk(e[2])
    BY EdgeIncreasesRank
  <1>3. ~IsCycleViaPath(edges)
    BY <1>1, <1>2, NoCycleByRank
  <1>4. QED BY <1>3 DEF IsConflictSerializableViaPath

----------------------------------------------------------------------------------------------------
(**************************************************************************************************)
(* Part 4.  The workload lemma: every TPC-C body satisfies H2 and H3.                             *)
(*                                                                                                *)
(* `BodyOK` is H2 and H3 phrased on a single body rather than on a history.  Going profile by      *)
(* profile:                                                                                       *)
(*                                                                                                *)
(*   New-Order    reads W_TAX, D_TAX, C.info and ITEM.info, all read-only for the whole           *)
(*                benchmark; its remaining reads (D_NEXT_O_ID, S_QUANTITY) are of keys it writes.  *)
(*   Payment      reads W_YTD, D_YTD, C_BALANCE and writes all three.                             *)
(*   Order-Status writes nothing, so H2 and H3 are vacuous.                                       *)
(*   Stock-Level  writes nothing, likewise.                                                       *)
(*                                                                                                *)
(* Delivery is the profile this fails for -- it reads ORDER.hdr and ORDERLINE.items, which        *)
(* New-Order writes, without writing them itself -- and `RobustMix` excludes it.                  *)
(**************************************************************************************************)

BodyOK(B) ==
    /\ \A w \in B.writes : ~ReadOnlyKey(w.key)
    /\ B.writes # {} =>
         \A k \in B.reads : k \in WriteKeysOf(B) \/ ReadOnlyKey(k)

\* Under column granularity a key carries its row's table and its own column.
LEMMA ItemOf ==
  ASSUME NEW base, NEW col, "tbl" \in DOMAIN base
  PROVE  Item(base, col).tbl = base.tbl /\ Item(base, col).col = col
PROOF
  <1>1. Item(base, col) = [x \in (DOMAIN base) \cup {"col"} |-> IF x = "col" THEN col ELSE base[x]]
    BY ColGran DEF Item
  <1>2. "tbl" \in (DOMAIN base) \cup {"col"} /\ "col" \in (DOMAIN base) \cup {"col"}
    OBVIOUS
  <1>3. QED BY <1>1, <1>2

\* The row-key constructors, and the fact that each names its table.
LEMMA KeyTables ==
  ASSUME NEW w, NEW d, NEW c, NEW i, NEW o, NEW t
  PROVE  /\ "tbl" \in DOMAIN WhKey(w)          /\ WhKey(w).tbl = "WH"
         /\ "tbl" \in DOMAIN DistKey(w,d)      /\ DistKey(w,d).tbl = "DIST"
         /\ "tbl" \in DOMAIN CustKey(w,d,c)    /\ CustKey(w,d,c).tbl = "CUST"
         /\ "tbl" \in DOMAIN ItemKey(i)        /\ ItemKey(i).tbl = "ITEM"
         /\ "tbl" \in DOMAIN StockKey(w,i)     /\ StockKey(w,i).tbl = "STOCK"
         /\ "tbl" \in DOMAIN OrderKey(w,d,o)   /\ OrderKey(w,d,o).tbl = "ORDER"
         /\ "tbl" \in DOMAIN NewOrdKey(w,d,o)  /\ NewOrdKey(w,d,o).tbl = "NEWORDER"
         /\ "tbl" \in DOMAIN OrdLineKey(w,d,o) /\ OrdLineKey(w,d,o).tbl = "ORDERLINE"
         /\ "tbl" \in DOMAIN HistKey(t)        /\ HistKey(t).tbl = "HIST"
PROOF
  BY DEF WhKey, DistKey, CustKey, ItemKey, StockKey,
         OrderKey, NewOrdKey, OrdLineKey, HistKey

\* Read and write key sets, unfolded under column granularity.
LEMMA RdKeysCol ==
  ASSUME NEW base, NEW cols
  PROVE  RdKeys(base, cols) = {Item(base, c) : c \in cols}
PROOF
  BY ColGran DEF RdKeys

LEMMA WrOpsCol ==
  ASSUME NEW snap, NEW base, NEW upd
  PROVE  /\ \A x \in WrOps(snap, base, upd) : \E c \in DOMAIN upd : x.key = Item(base, c)
         /\ \A c \in DOMAIN upd :
              \E x \in WrOps(snap, base, upd) : x.key = Item(base, c)
PROOF
  <1>1. WrOps(snap, base, upd)
          = {[type |-> "write", key |-> Item(base, c), val |-> upd[c]] : c \in DOMAIN upd}
    BY ColGran DEF WrOps
  <1>2. QED BY <1>1

(*----------------------------------------------------------------------------------------------*)
(* NEW-ORDER                                                                                     *)
(*----------------------------------------------------------------------------------------------*)
LEMMA NewOrderOK ==
  ASSUME NEW req, NEW snap
  PROVE  BodyOK(NewOrderProgram(req, snap))
PROOF
  <1> DEFINE w == req.w   d == req.d   c == req.c   sw == req.sw   items == req.items
             o == ColVal(snap, DistKey(w,d), "nextoid")
             B == NewOrderProgram(req, snap)
             WD == WrOps(snap, DistKey(w,d), [nextoid |-> o + 1])
             WS == UNION {WrOps(snap, StockKey(sw,i), [qty |-> Tag]) : i \in items}
             WO == WrOps(snap, OrderKey(w,d,o),   [hdr |-> c, carrier |-> Tag])
             WN == WrOps(snap, NewOrdKey(w,d,o),  [row |-> Tag])
             WL == WrOps(snap, OrdLineKey(w,d,o), [items |-> items, delivery |-> Tag])
  <1>1. B.reads = RdKeys(WhKey(w), {"tax"})
                    \cup RdKeys(DistKey(w,d), {"tax", "nextoid"})
                    \cup RdKeys(CustKey(w,d,c), {"info"})
                    \cup (UNION {RdKeys(ItemKey(i), {"info"}) : i \in items})
                    \cup (UNION {RdKeys(StockKey(sw,i), {"qty"}) : i \in items})
    BY DEF NewOrderProgram
  <1>2. B.writes = WD \cup WS \cup WO \cup WN \cup WL
    BY DEF NewOrderProgram
  \* ---- H2: no write lands on a read-only column group.
  <1>3. \A x \in B.writes : ~ReadOnlyKey(x.key)
    <2>1. SUFFICES ASSUME NEW x \in B.writes PROVE ~ReadOnlyKey(x.key) OBVIOUS
    <2>2. CASE x \in WD
      <3>1. PICK cc \in DOMAIN [nextoid |-> o + 1] : x.key = Item(DistKey(w,d), cc)
        BY <2>2, WrOpsCol
      <3>2. cc = "nextoid" BY <3>1
      <3>3. x.key.tbl = "DIST" /\ x.key.col = "nextoid"
        BY <3>1, <3>2, ItemOf, KeyTables
      <3>4. QED BY <3>3 DEF ReadOnlyKey
    <2>3. CASE x \in WS
      <3>1. PICK i \in items : x \in WrOps(snap, StockKey(sw,i), [qty |-> Tag])
        BY <2>3
      <3>2. PICK cc \in DOMAIN [qty |-> Tag] : x.key = Item(StockKey(sw,i), cc)
        BY <3>1, WrOpsCol
      <3>3. x.key.tbl = "STOCK" BY <3>2, ItemOf, KeyTables
      <3>4. QED BY <3>3 DEF ReadOnlyKey
    <2>4. CASE x \in WO
      <3>1. PICK cc \in DOMAIN [hdr |-> c, carrier |-> Tag] : x.key = Item(OrderKey(w,d,o), cc)
        BY <2>4, WrOpsCol
      <3>2. x.key.tbl = "ORDER" BY <3>1, ItemOf, KeyTables
      <3>3. QED BY <3>2 DEF ReadOnlyKey
    <2>5. CASE x \in WN
      <3>1. PICK cc \in DOMAIN [row |-> Tag] : x.key = Item(NewOrdKey(w,d,o), cc)
        BY <2>5, WrOpsCol
      <3>2. x.key.tbl = "NEWORDER" BY <3>1, ItemOf, KeyTables
      <3>3. QED BY <3>2 DEF ReadOnlyKey
    <2>6. CASE x \in WL
      <3>1. PICK cc \in DOMAIN [items |-> items, delivery |-> Tag] :
              x.key = Item(OrdLineKey(w,d,o), cc)
        BY <2>6, WrOpsCol
      <3>2. x.key.tbl = "ORDERLINE" BY <3>1, ItemOf, KeyTables
      <3>3. QED BY <3>2 DEF ReadOnlyKey
    <2>7. QED BY <1>2, <2>2, <2>3, <2>4, <2>5, <2>6
  \* ---- H3: every read is of a key written, or of a read-only key.
  <1>4. \A k \in B.reads : k \in WriteKeysOf(B) \/ ReadOnlyKey(k)
    <2>1. SUFFICES ASSUME NEW k \in B.reads
                   PROVE  k \in WriteKeysOf(B) \/ ReadOnlyKey(k)
      OBVIOUS
    <2>2. CASE k \in RdKeys(WhKey(w), {"tax"})
      <3>1. k = Item(WhKey(w), "tax") BY <2>2, RdKeysCol
      <3>2. k.tbl = "WH" /\ k.col = "tax" BY <3>1, ItemOf, KeyTables
      <3>3. QED BY <3>2 DEF ReadOnlyKey
    <2>3. CASE k \in RdKeys(DistKey(w,d), {"tax", "nextoid"})
      <3>1. PICK cc \in {"tax", "nextoid"} : k = Item(DistKey(w,d), cc)
        BY <2>3, RdKeysCol
      <3>2. CASE cc = "tax"
        <4>1. k.tbl = "DIST" /\ k.col = "tax" BY <3>1, <3>2, ItemOf, KeyTables
        <4>2. QED BY <4>1 DEF ReadOnlyKey
      <3>3. CASE cc = "nextoid"
        <4>1. "nextoid" \in DOMAIN [nextoid |-> o + 1] OBVIOUS
        <4>2. PICK x \in WD : x.key = Item(DistKey(w,d), "nextoid")
          BY <4>1, WrOpsCol
        <4>3. x \in B.writes BY <1>2, <4>2
        <4>4. QED BY <3>1, <3>3, <4>2, <4>3 DEF WriteKeysOf
      <3>4. QED BY <3>1, <3>2, <3>3
    <2>4. CASE k \in RdKeys(CustKey(w,d,c), {"info"})
      <3>1. k = Item(CustKey(w,d,c), "info") BY <2>4, RdKeysCol
      <3>2. k.tbl = "CUST" /\ k.col = "info" BY <3>1, ItemOf, KeyTables
      <3>3. QED BY <3>2 DEF ReadOnlyKey
    <2>5. CASE k \in UNION {RdKeys(ItemKey(i), {"info"}) : i \in items}
      <3>1. PICK i \in items : k \in RdKeys(ItemKey(i), {"info"}) BY <2>5
      <3>2. k = Item(ItemKey(i), "info") BY <3>1, RdKeysCol
      <3>3. k.tbl = "ITEM" BY <3>2, ItemOf, KeyTables
      <3>4. QED BY <3>3 DEF ReadOnlyKey
    <2>6. CASE k \in UNION {RdKeys(StockKey(sw,i), {"qty"}) : i \in items}
      <3>1. PICK i \in items : k \in RdKeys(StockKey(sw,i), {"qty"}) BY <2>6
      <3>2. k = Item(StockKey(sw,i), "qty") BY <3>1, RdKeysCol
      <3>3. "qty" \in DOMAIN [qty |-> Tag] OBVIOUS
      <3>4. PICK x \in WrOps(snap, StockKey(sw,i), [qty |-> Tag]) :
              x.key = Item(StockKey(sw,i), "qty")
        BY <3>3, WrOpsCol
      <3>5. x \in WS BY <3>1, <3>4
      <3>6. x \in B.writes BY <1>2, <3>5
      <3>7. QED BY <3>2, <3>4, <3>6 DEF WriteKeysOf
    <2>7. QED BY <1>1, <2>2, <2>3, <2>4, <2>5, <2>6
  <1>5. QED BY <1>3, <1>4 DEF BodyOK

(*----------------------------------------------------------------------------------------------*)
(* PAYMENT                                                                                       *)
(*----------------------------------------------------------------------------------------------*)
LEMMA PaymentOK ==
  ASSUME NEW tid, NEW req, NEW snap
  PROVE  BodyOK(PaymentProgram(tid, req, snap))
PROOF
  <1> DEFINE w == req.w   d == req.d   cw == req.cw   cd == req.cd   c == req.c
             B == PaymentProgram(tid, req, snap)
             WW == WrOps(snap, WhKey(w), [ytd |-> Tag])
             WD == WrOps(snap, DistKey(w,d), [ytd |-> Tag])
             WC == WrOps(snap, CustKey(cw,cd,c), [balance |-> Tag])
             WH == WrOps(snap, HistKey(tid), [row |-> Tag])
  <1>1. B.reads = RdKeys(WhKey(w), {"ytd"})
                    \cup RdKeys(DistKey(w,d), {"ytd"})
                    \cup RdKeys(CustKey(cw,cd,c), {"balance"})
    BY DEF PaymentProgram
  <1>2. B.writes = WW \cup WD \cup WC \cup WH
    BY DEF PaymentProgram
  \* ---- H2.
  <1>3. \A x \in B.writes : ~ReadOnlyKey(x.key)
    <2>1. SUFFICES ASSUME NEW x \in B.writes PROVE ~ReadOnlyKey(x.key) OBVIOUS
    <2>2. CASE x \in WW
      <3>1. PICK cc \in DOMAIN [ytd |-> Tag] : x.key = Item(WhKey(w), cc)
        BY <2>2, WrOpsCol
      <3>2. x.key.tbl = "WH" /\ x.key.col = "ytd" BY <3>1, ItemOf, KeyTables
      <3>3. QED BY <3>2 DEF ReadOnlyKey
    <2>3. CASE x \in WD
      <3>1. PICK cc \in DOMAIN [ytd |-> Tag] : x.key = Item(DistKey(w,d), cc)
        BY <2>3, WrOpsCol
      <3>2. x.key.tbl = "DIST" /\ x.key.col = "ytd" BY <3>1, ItemOf, KeyTables
      <3>3. QED BY <3>2 DEF ReadOnlyKey
    <2>4. CASE x \in WC
      <3>1. PICK cc \in DOMAIN [balance |-> Tag] : x.key = Item(CustKey(cw,cd,c), cc)
        BY <2>4, WrOpsCol
      <3>2. x.key.tbl = "CUST" /\ x.key.col = "balance" BY <3>1, ItemOf, KeyTables
      <3>3. QED BY <3>2 DEF ReadOnlyKey
    <2>5. CASE x \in WH
      <3>1. PICK cc \in DOMAIN [row |-> Tag] : x.key = Item(HistKey(tid), cc)
        BY <2>5, WrOpsCol
      <3>2. x.key.tbl = "HIST" BY <3>1, ItemOf, KeyTables
      <3>3. QED BY <3>2 DEF ReadOnlyKey
    <2>6. QED BY <1>2, <2>2, <2>3, <2>4, <2>5
  \* ---- H3: all three reads are of keys Payment itself writes.
  <1>4. \A k \in B.reads : k \in WriteKeysOf(B) \/ ReadOnlyKey(k)
    <2>1. SUFFICES ASSUME NEW k \in B.reads PROVE k \in WriteKeysOf(B) OBVIOUS
    <2>2. CASE k \in RdKeys(WhKey(w), {"ytd"})
      <3>1. k = Item(WhKey(w), "ytd") BY <2>2, RdKeysCol
      <3>2. "ytd" \in DOMAIN [ytd |-> Tag] OBVIOUS
      <3>3. PICK x \in WW : x.key = Item(WhKey(w), "ytd") BY <3>2, WrOpsCol
      <3>4. QED BY <1>2, <3>1, <3>3 DEF WriteKeysOf
    <2>3. CASE k \in RdKeys(DistKey(w,d), {"ytd"})
      <3>1. k = Item(DistKey(w,d), "ytd") BY <2>3, RdKeysCol
      <3>2. "ytd" \in DOMAIN [ytd |-> Tag] OBVIOUS
      <3>3. PICK x \in WD : x.key = Item(DistKey(w,d), "ytd") BY <3>2, WrOpsCol
      <3>4. QED BY <1>2, <3>1, <3>3 DEF WriteKeysOf
    <2>4. CASE k \in RdKeys(CustKey(cw,cd,c), {"balance"})
      <3>1. k = Item(CustKey(cw,cd,c), "balance") BY <2>4, RdKeysCol
      <3>2. "balance" \in DOMAIN [balance |-> Tag] OBVIOUS
      <3>3. PICK x \in WC : x.key = Item(CustKey(cw,cd,c), "balance") BY <3>2, WrOpsCol
      <3>4. QED BY <1>2, <3>1, <3>3 DEF WriteKeysOf
    <2>5. QED BY <1>1, <2>2, <2>3, <2>4
  <1>6. QED BY <1>3, <1>4 DEF BodyOK

(*----------------------------------------------------------------------------------------------*)
(* The two read-only profiles.                                                                   *)
(*----------------------------------------------------------------------------------------------*)
LEMMA OrderStatusOK ==
  ASSUME NEW req, NEW snap
  PROVE  /\ BodyOK(OrderStatusProgram(req, snap))
         /\ OrderStatusProgram(req, snap).writes = {}
PROOF
  <1>1. OrderStatusProgram(req, snap).writes = {} BY DEF OrderStatusProgram
  <1>2. WriteKeysOf(OrderStatusProgram(req, snap)) = {} BY <1>1 DEF WriteKeysOf
  <1>3. QED BY <1>1, <1>2 DEF BodyOK

LEMMA StockLevelOK ==
  ASSUME NEW req, NEW snap
  PROVE  /\ BodyOK(StockLevelProgram(req, snap))
         /\ StockLevelProgram(req, snap).writes = {}
PROOF
  <1>1. StockLevelProgram(req, snap).writes = {} BY DEF StockLevelProgram
  <1>2. WriteKeysOf(StockLevelProgram(req, snap)) = {} BY <1>1 DEF WriteKeysOf
  <1>3. QED BY <1>1, <1>2 DEF BodyOK

(*----------------------------------------------------------------------------------------------*)
(* Assembly: `RobustMix` leaves exactly the four profiles above.                                  *)
(*----------------------------------------------------------------------------------------------*)
LEMMA ReqTypes ==
  \A req \in Requests : req.type \in {"NewOrder", "Payment", "OrderStatus", "StockLevel"}
PROOF
  <1>1. SUFFICES ASSUME NEW req \in Requests
                 PROVE  req.type \in {"NewOrder", "Payment", "OrderStatus", "StockLevel"}
    OBVIOUS
  <1>2. "Delivery" \notin EnabledTxnTypes BY RobustMix
  <1>3. QED BY <1>2 DEF Requests

THEOREM WorkloadSubsumed ==
  ASSUME NEW tid, NEW req \in Requests, NEW snap
  PROVE  BodyOK(ProgramFor(tid, req, snap))
PROOF
  <1>1. req.type \in {"NewOrder", "Payment", "OrderStatus", "StockLevel"} BY ReqTypes
  <1>2. CASE req.type = "NewOrder"
    BY <1>2, NewOrderOK DEF ProgramFor
  <1>3. CASE req.type = "Payment"
    BY <1>3, PaymentOK DEF ProgramFor
  <1>4. CASE req.type = "OrderStatus"
    BY <1>4, OrderStatusOK DEF ProgramFor
  <1>5. CASE req.type = "StockLevel"
    BY <1>5, StockLevelOK DEF ProgramFor
  <1>6. QED BY <1>1, <1>2, <1>3, <1>4, <1>5

----------------------------------------------------------------------------------------------------
(**************************************************************************************************)
(* Part 5.  Sequence infrastructure.                                                              *)
(**************************************************************************************************)

IsSeq(h) == \E S : h \in Seq(S)

LEMMA EmptyIsSeq == IsSeq(<<>>)
PROOF
  <1>1. <<>> \in Seq({}) BY EmptySeq
  <1>2. QED BY <1>1 DEF IsSeq

LEMMA AppendIsSeq ==
  ASSUME NEW h, IsSeq(h), NEW o
  PROVE  /\ IsSeq(Append(h, o))
         /\ Range(Append(h, o)) = Range(h) \cup {o}
PROOF
  <1>1. PICK S : h \in Seq(S) BY DEF IsSeq
  <1>2. h \in Seq(S \cup {o}) BY <1>1, SeqMonotonic
  <1>3. o \in S \cup {o} OBVIOUS
  <1>4. /\ Append(h, o) \in Seq(S \cup {o})
        /\ Range(Append(h, o)) = Range(h) \cup {o}
    BY <1>2, <1>3, AppendProperties
  <1>5. QED BY <1>4 DEF IsSeq

\* `StartAndRun` appends two operations at once.
LEMMA Append2IsSeq ==
  ASSUME NEW h, IsSeq(h), NEW o1, NEW o2
  PROVE  /\ IsSeq(h \o <<o1, o2>>)
         /\ Range(h \o <<o1, o2>>) = Range(h) \cup {o1, o2}
PROOF
  <1>1. PICK S : h \in Seq(S) BY DEF IsSeq
  <1> DEFINE T == S \cup {o1, o2}
  <1>2. h \in Seq(T) BY <1>1, SeqMonotonic
  <1>3. <<o1, o2>> \in Seq(T)
    <2>1. <<o1, o2>> \in [1..2 -> T] BY DEF Seq
    <2>2. QED BY <2>1, IsASeq
  <1>4. h \o <<o1, o2>> \in Seq(T) BY <1>2, <1>3, ConcatProperties
  <1>5. Range(h \o <<o1, o2>>) = Range(h) \cup Range(<<o1, o2>>)
    BY <1>2, <1>3, RangeConcatenation
  <1>6. Range(<<o1, o2>>) = {o1, o2}
    <2>1. <<o1, o2>> \in Seq(T) BY <1>3
    <2>2. DOMAIN <<o1, o2>> = 1..2 BY DEF Seq
    <2>3. QED BY <2>2 DEF Range
  <1>7. QED BY <1>4, <1>5, <1>6 DEF IsSeq

----------------------------------------------------------------------------------------------------
(**************************************************************************************************)
(* Part 6.  The inductive invariant.                                                              *)
(*                                                                                                *)
(* Everything is stated over the *range* of the history, never through `BeginOp` / `CommitOp`.     *)
(* Those two are `CHOOSE`s, and a `CHOOSE` over a growing set needs a uniqueness argument at      *)
(* every step; quantifying over operations instead and converting once, in Part 7, confines that   *)
(* reasoning to one place.                                                                        *)
(**************************************************************************************************)

OpTypes == {"begin", "body", "commit", "abort"}

\* The unique begin / body / commit op of a transaction, as a predicate over the range.
HasOp(h, t, ty) == \E op \in Range(h) : op.txnId = t /\ op.type = ty

Inv ==
    /\ clock \in Nat
    /\ IsSeq(txnHistory)
    \* ---- shape
    /\ \A op \in Range(txnHistory) : op.type \in OpTypes
    /\ \A op \in Range(txnHistory) :
         op.type \in {"begin", "commit"} => op.time \in 1..clock
    \* ---- at most one begin / body / commit op per transaction
    /\ \A o1, o2 \in Range(txnHistory) :
         o1.txnId = o2.txnId /\ o1.type = o2.type /\ o1.type \in {"begin", "body", "commit"}
           => o1 = o2
    \* ---- H1, as a relation between a transaction's begin and commit ops
    /\ \A ob, oc \in Range(txnHistory) :
         /\ ob.type = "begin" /\ oc.type = "commit" /\ ob.txnId = oc.txnId
         => ob.time < oc.time
    \* ---- a committed transaction has a begin op and a body op
    /\ \A oc \in Range(txnHistory) :
         oc.type = "commit" => HasOp(txnHistory, oc.txnId, "begin")
                            /\ HasOp(txnHistory, oc.txnId, "body")
    \* ---- H2 and H3, via the workload lemma
    /\ \A ob \in Range(txnHistory) : ob.type = "body" => BodyOK(ob)
    \* ---- a commit op records exactly the keys its transaction wrote
    /\ \A oc \in Range(txnHistory) :
         oc.type = "commit" => oc.updatedKeys = {k \in Keys : WritesKey(txnHistory, oc.txnId, k)}
    \* ---- H4: First-Committer-Wins.  Two commits sharing a written key have disjoint lifetimes.
    /\ \A o1, o2 \in Range(txnHistory) :
         /\ o1.type = "commit" /\ o2.type = "commit" /\ o1.txnId # o2.txnId
         /\ o1.updatedKeys \cap o2.updatedKeys # {}
         => \/ \E b2 \in Range(txnHistory) :
                 b2.type = "begin" /\ b2.txnId = o2.txnId /\ o1.time =< b2.time
            \/ \E b1 \in Range(txnHistory) :
                 b1.type = "begin" /\ b1.txnId = o1.txnId /\ o2.time =< b1.time
    \* ---- running transactions: each has a begin op recording its start time, and has not
    \*      committed yet
    /\ \A r \in runningTxns :
         /\ r.id \in TxnIds
         /\ r.startTime \in 1..clock
         /\ \E ob \in Range(txnHistory) :
              ob.type = "begin" /\ ob.txnId = r.id /\ ob.time = r.startTime
         /\ HasOp(txnHistory, r.id, "body")
         /\ ~HasOp(txnHistory, r.id, "commit")

----------------------------------------------------------------------------------------------------
(**************************************************************************************************)
(* Part 7.  `Inv` implies `HistoryOK`, hence `SerializableViaPath`.                               *)
(*                                                                                                *)
(* This is where `BeginOp` and `CommitOp` -- both `CHOOSE`s -- are pinned down.  Uniqueness of a   *)
(* transaction's begin and commit ops is a clause of `Inv`, so each `CHOOSE` picks the only        *)
(* candidate.                                                                                     *)
(**************************************************************************************************)

LEMMA ChoosePins ==
  ASSUME NEW P(_), NEW x, P(x), \A y, z : P(y) /\ P(z) => y = z
  PROVE  (CHOOSE y : P(y)) = x
PROOF
  <1>1. P(CHOOSE y : P(y)) BY Zenon
  <1>2. QED BY <1>1

\* The begin op of a committed transaction is the unique begin op carrying its id.
LEMMA BeginOpIs ==
  ASSUME Inv, NEW t, NEW ob \in Range(txnHistory), ob.type = "begin", ob.txnId = t
  PROVE  BeginOp(txnHistory, t) = ob
PROOF
  <1> DEFINE P(x) == x \in Range(txnHistory) /\ x.txnId = t /\ x.type = "begin"
  <1>1. P(ob) OBVIOUS
  <1>2. \A y, z : P(y) /\ P(z) => y = z BY DEF Inv
  <1>3. (CHOOSE y : P(y)) = ob BY <1>1, <1>2, ChoosePins
  <1>4. QED BY <1>3 DEF BeginOp

LEMMA CommitOpIs ==
  ASSUME Inv, NEW t, NEW oc \in Range(txnHistory), oc.type = "commit", oc.txnId = t
  PROVE  CommitOp(txnHistory, t) = oc
PROOF
  <1> DEFINE P(x) == x \in Range(txnHistory) /\ x.txnId = t /\ x.type = "commit"
  <1>1. P(oc) OBVIOUS
  <1>2. \A y, z : P(y) /\ P(z) => y = z BY DEF Inv
  <1>3. (CHOOSE y : P(y)) = oc BY <1>1, <1>2, ChoosePins
  <1>4. QED BY <1>3 DEF CommitOp

\* Every committed transaction has a commit op, and a begin op.
LEMMA CommittedHasOps ==
  ASSUME Inv, NEW t \in CommittedTxns(txnHistory)
  PROVE  /\ \E oc \in Range(txnHistory) : oc.type = "commit" /\ oc.txnId = t
         /\ \E ob \in Range(txnHistory) : ob.type = "begin"  /\ ob.txnId = t
         /\ \E oy \in Range(txnHistory) : oy.type = "body"   /\ oy.txnId = t
PROOF
  <1>1. PICK oc \in Range(txnHistory) : oc.type = "commit" /\ oc.txnId = t
    BY DEF CommittedTxns
  <1>2. HasOp(txnHistory, t, "begin") /\ HasOp(txnHistory, t, "body")
    BY <1>1 DEF Inv
  <1>3. QED BY <1>1, <1>2 DEF HasOp

\* A transaction's written-key set equals the `updatedKeys` its commit op records.
LEMMA WKeysAreUpdatedKeys ==
  ASSUME Inv, NEW t, NEW oc \in Range(txnHistory), oc.type = "commit", oc.txnId = t
  PROVE  oc.updatedKeys = {k \in Keys : WritesKey(txnHistory, t, k)}
PROOF
  BY DEF Inv

\* H2 and H3 transfer from the body op to the history-level predicates.
LEMMA BodyGivesH2H3 ==
  ASSUME Inv, NEW t, NEW oy \in Range(txnHistory), oy.type = "body", oy.txnId = t
  PROVE  /\ \A k \in Keys : WritesKey(txnHistory, t, k) => ~ReadOnlyKey(k)
         /\ Updater(txnHistory, t) =>
              \A k \in Keys : ReadsKey(txnHistory, t, k) =>
                  (WritesKey(txnHistory, t, k) \/ ReadOnlyKey(k))
PROOF
  <1>1. BodyOK(oy) BY DEF Inv
  \* Any body op of t is oy, by uniqueness.
  <1>2. \A o \in Range(txnHistory) : o.type = "body" /\ o.txnId = t => o = oy
    BY DEF Inv
  <1>3. \A k : WritesKey(txnHistory, t, k) <=> (\E w \in oy.writes : w.key = k)
    <2>1. SUFFICES ASSUME NEW k
                   PROVE  WritesKey(txnHistory, t, k) <=> (\E w \in oy.writes : w.key = k)
      OBVIOUS
    <2>2. ASSUME WritesKey(txnHistory, t, k)
          PROVE  \E w \in oy.writes : w.key = k
      <3>1. PICK o \in Range(txnHistory) :
              o.txnId = t /\ o.type = "body" /\ \E w \in o.writes : w.key = k
        BY <2>2 DEF WritesKey
      <3>2. o = oy BY <3>1, <1>2
      <3>3. QED BY <3>1, <3>2
    <2>3. ASSUME \E w \in oy.writes : w.key = k
          PROVE  WritesKey(txnHistory, t, k)
      BY <2>3 DEF WritesKey
    <2>4. QED BY <2>2, <2>3
  <1>4. \A k : ReadsKey(txnHistory, t, k) <=> k \in oy.reads
    <2>1. SUFFICES ASSUME NEW k
                   PROVE  ReadsKey(txnHistory, t, k) <=> k \in oy.reads
      OBVIOUS
    <2>2. ASSUME ReadsKey(txnHistory, t, k) PROVE k \in oy.reads
      <3>1. PICK o \in Range(txnHistory) : o.txnId = t /\ o.type = "body" /\ k \in o.reads
        BY <2>2 DEF ReadsKey
      <3>2. o = oy BY <3>1, <1>2
      <3>3. QED BY <3>1, <3>2
    <2>3. ASSUME k \in oy.reads PROVE ReadsKey(txnHistory, t, k)
      BY <2>3 DEF ReadsKey
    <2>4. QED BY <2>2, <2>3
  \* ---- H2.
  <1>5. \A k \in Keys : WritesKey(txnHistory, t, k) => ~ReadOnlyKey(k)
    <2>1. SUFFICES ASSUME NEW k \in Keys, WritesKey(txnHistory, t, k)
                   PROVE  ~ReadOnlyKey(k)
      OBVIOUS
    <2>2. PICK w \in oy.writes : w.key = k BY <2>1, <1>3
    <2>3. ~ReadOnlyKey(w.key) BY <1>1, <2>2 DEF BodyOK
    <2>4. QED BY <2>2, <2>3
  \* ---- H3.
  <1>6. Updater(txnHistory, t) =>
          \A k \in Keys : ReadsKey(txnHistory, t, k) =>
              (WritesKey(txnHistory, t, k) \/ ReadOnlyKey(k))
    <2>1. SUFFICES ASSUME Updater(txnHistory, t), NEW k \in Keys,
                          ReadsKey(txnHistory, t, k), ~ReadOnlyKey(k)
                   PROVE  WritesKey(txnHistory, t, k)
      OBVIOUS
    <2>2. oy.writes # {}
      <3>1. PICK kk \in Keys : WritesKey(txnHistory, t, kk) BY <2>1 DEF Updater
      <3>2. PICK w \in oy.writes : w.key = kk BY <3>1, <1>3
      <3>3. QED BY <3>2
    <2>3. k \in oy.reads BY <2>1, <1>4
    <2>4a. \A kk \in oy.reads : kk \in WriteKeysOf(oy) \/ ReadOnlyKey(kk)
      BY <1>1, <2>2 DEF BodyOK
    <2>4. k \in WriteKeysOf(oy) BY <2>4a, <2>3, <2>1
    <2>5. PICK w \in oy.writes : w.key = k BY <2>4 DEF WriteKeysOf
    <2>6. QED BY <2>5, <1>3
  <1>7. QED BY <1>5, <1>6

THEOREM InvImpliesHistoryOK == Inv => HistoryOK(txnHistory)
PROOF
  <1> SUFFICES ASSUME Inv,
                      NEW t1 \in CommittedTxns(txnHistory),
                      NEW t2 \in CommittedTxns(txnHistory)
               PROVE  /\ BeginOp(txnHistory, t1).time \in Nat
                      /\ CommitOp(txnHistory, t1).time \in Nat
                      /\ BeginOp(txnHistory, t1).time < CommitOp(txnHistory, t1).time
                      /\ \A k \in Keys : WritesKey(txnHistory, t1, k) => ~ReadOnlyKey(k)
                      /\ Updater(txnHistory, t1) =>
                           \A k \in Keys : ReadsKey(txnHistory, t1, k) =>
                               (WritesKey(txnHistory, t1, k) \/ ReadOnlyKey(k))
                      /\ (t1 # t2 /\ (\E k \in Keys : WritesKey(txnHistory, t1, k)
                                                   /\ WritesKey(txnHistory, t2, k)))
                           => \/ CommitOp(txnHistory, t1).time =< BeginOp(txnHistory, t2).time
                              \/ CommitOp(txnHistory, t2).time =< BeginOp(txnHistory, t1).time
    BY DEF HistoryOK
  <1>1. PICK c1 \in Range(txnHistory) : c1.type = "commit" /\ c1.txnId = t1
    BY CommittedHasOps
  <1>2. PICK b1 \in Range(txnHistory) : b1.type = "begin" /\ b1.txnId = t1
    BY CommittedHasOps
  <1>3. PICK c2 \in Range(txnHistory) : c2.type = "commit" /\ c2.txnId = t2
    BY CommittedHasOps
  <1>4. PICK b2 \in Range(txnHistory) : b2.type = "begin" /\ b2.txnId = t2
    BY CommittedHasOps
  <1>5. /\ CommitOp(txnHistory, t1) = c1 /\ BeginOp(txnHistory, t1) = b1
        /\ CommitOp(txnHistory, t2) = c2 /\ BeginOp(txnHistory, t2) = b2
    BY <1>1, <1>2, <1>3, <1>4, CommitOpIs, BeginOpIs
  <1>6. /\ c1.time \in Nat /\ b1.time \in Nat
        /\ c2.time \in Nat /\ b2.time \in Nat
    BY <1>1, <1>2, <1>3, <1>4 DEF Inv
  \* ---- H1.
  <1>7. b1.time < c1.time BY <1>1, <1>2 DEF Inv
  \* ---- H2, H3.
  <1>8. /\ \A k \in Keys : WritesKey(txnHistory, t1, k) => ~ReadOnlyKey(k)
        /\ Updater(txnHistory, t1) =>
             \A k \in Keys : ReadsKey(txnHistory, t1, k) =>
                 (WritesKey(txnHistory, t1, k) \/ ReadOnlyKey(k))
    <2>1. PICK y1 \in Range(txnHistory) : y1.type = "body" /\ y1.txnId = t1
      BY CommittedHasOps
    <2>2. QED BY <2>1, BodyGivesH2H3
  \* ---- H4.
  <1>9. (t1 # t2 /\ (\E k \in Keys : WritesKey(txnHistory, t1, k)
                                  /\ WritesKey(txnHistory, t2, k)))
          => c1.time =< b2.time \/ c2.time =< b1.time
    <2>1. SUFFICES ASSUME t1 # t2,
                          NEW k \in Keys,
                          WritesKey(txnHistory, t1, k), WritesKey(txnHistory, t2, k)
                   PROVE  c1.time =< b2.time \/ c2.time =< b1.time
      OBVIOUS
    <2>2. c1.updatedKeys = {kk \in Keys : WritesKey(txnHistory, t1, kk)}
      BY <1>1, WKeysAreUpdatedKeys
    <2>3. c2.updatedKeys = {kk \in Keys : WritesKey(txnHistory, t2, kk)}
      BY <1>3, WKeysAreUpdatedKeys
    <2>4. k \in c1.updatedKeys /\ k \in c2.updatedKeys BY <2>1, <2>2, <2>3
    <2>5. c1.updatedKeys \cap c2.updatedKeys # {} BY <2>4
    <2>6. \/ \E x \in Range(txnHistory) :
                x.type = "begin" /\ x.txnId = t2 /\ c1.time =< x.time
          \/ \E x \in Range(txnHistory) :
                x.type = "begin" /\ x.txnId = t1 /\ c2.time =< x.time
      BY <1>1, <1>3, <2>1, <2>5 DEF Inv
    <2>7. CASE \E x \in Range(txnHistory) :
                 x.type = "begin" /\ x.txnId = t2 /\ c1.time =< x.time
      <3>1. PICK x \in Range(txnHistory) :
              x.type = "begin" /\ x.txnId = t2 /\ c1.time =< x.time
        BY <2>7
      <3>2. x = b2 BY <3>1, <1>4 DEF Inv
      <3>3. QED BY <3>1, <3>2
    <2>8. CASE \E x \in Range(txnHistory) :
                 x.type = "begin" /\ x.txnId = t1 /\ c2.time =< x.time
      <3>1. PICK x \in Range(txnHistory) :
              x.type = "begin" /\ x.txnId = t1 /\ c2.time =< x.time
        BY <2>8
      <3>2. x = b1 BY <3>1, <1>2 DEF Inv
      <3>3. QED BY <3>1, <3>2
    <2>9. QED BY <2>6, <2>7, <2>8
  <1>10. QED BY <1>5, <1>6, <1>7, <1>8, <1>9

THEOREM InvImpliesSerializable == Inv => SerializableViaPath
PROOF
  BY InvImpliesHistoryOK, HistoryOKImpliesSerializable DEF SerializableViaPath

----------------------------------------------------------------------------------------------------
(**************************************************************************************************)
(* Part 8.  The initial state.                                                                    *)
(**************************************************************************************************)

THEOREM InitInv == Init => Inv
PROOF
  <1> SUFFICES ASSUME Init PROVE Inv OBVIOUS
  <1>1. txnHistory = <<>> /\ clock = 0 /\ runningTxns = {} BY DEF Init
  <1>2. Range(txnHistory) = {} BY <1>1, EmptyRange
  <1>3. IsSeq(txnHistory) BY <1>1, EmptyIsSeq
  <1>4. QED BY <1>1, <1>2, <1>3 DEF Inv

----------------------------------------------------------------------------------------------------
(**************************************************************************************************)
(* Part 9.  Abort.                                                                                *)
(*                                                                                                *)
(* `AbortTxn` appends an "abort" op.  Nothing in `Inv` constrains abort ops beyond their type, so *)
(* each clause either quantifies over operations the new one is not (every other clause filters    *)
(* on a type in {begin, body, commit}) or is about `clock`, which only grows.                     *)
(**************************************************************************************************)

\* Writing/reading a key is unaffected by appending a non-body op.
LEMMA RWSameAppend ==
  ASSUME NEW h, IsSeq(h), NEW o, o.type # "body"
  PROVE  /\ \A t, k : WritesKey(Append(h, o), t, k) <=> WritesKey(h, t, k)
         /\ \A t, k : ReadsKey(Append(h, o), t, k)  <=> ReadsKey(h, t, k)
PROOF
  <1>1. Range(Append(h, o)) = Range(h) \cup {o} BY AppendIsSeq
  <1>2. QED BY <1>1 DEF WritesKey, ReadsKey

\* Likewise the committed set is unaffected by appending a non-commit op.
LEMMA CommittedSameAppend ==
  ASSUME NEW h, IsSeq(h), NEW o, o.type # "commit"
  PROVE  CommittedTxns(Append(h, o)) = CommittedTxns(h)
PROOF
  <1>1. Range(Append(h, o)) = Range(h) \cup {o} BY AppendIsSeq
  <1>2. {op \in Range(Append(h, o)) : op.type = "commit"}
          = {op \in Range(h) : op.type = "commit"}
    BY <1>1
  <1>3. QED BY <1>2 DEF CommittedTxns

THEOREM StepAbort ==
  ASSUME Inv, NEW tid, AbortTxn(tid)
  PROVE  Inv'
PROOF
  <1> DEFINE o == [type |-> "abort", txnId |-> tid, time |-> clock + 1]
  <1>1. /\ txnHistory' = Append(txnHistory, o)
        /\ clock' = clock + 1
        /\ runningTxns' = {r \in runningTxns : r.id # tid}
        /\ dataStore' = dataStore
    BY DEF AbortTxn
  <1>2. clock \in Nat /\ IsSeq(txnHistory) BY DEF Inv
  <1>3. clock' \in Nat BY <1>1, <1>2
  <1>4. IsSeq(txnHistory') /\ Range(txnHistory') = Range(txnHistory) \cup {o}
    BY <1>1, <1>2, AppendIsSeq
  <1>5. o.type = "abort" /\ o.type \notin {"begin", "body", "commit"} OBVIOUS
  \* The new op is filtered out of every clause that quantifies over typed ops.
  <1>6. /\ \A op \in Range(txnHistory') : op.type \in OpTypes
        /\ \A op \in Range(txnHistory') :
             op.type \in {"begin", "commit"} => op.time \in 1..clock'
    <2>1. \A op \in Range(txnHistory) : op.type \in OpTypes BY DEF Inv
    <2>2. \A op \in Range(txnHistory) :
            op.type \in {"begin", "commit"} => op.time \in 1..clock
      BY DEF Inv
    <2>3. 1..clock \subseteq 1..clock' BY <1>1, <1>2
    <2>4. QED BY <1>4, <1>5, <2>1, <2>2, <2>3 DEF OpTypes
  <1>7. \A t, k : WritesKey(txnHistory', t, k) <=> WritesKey(txnHistory, t, k)
    BY <1>1, <1>2, <1>5, RWSameAppend
  \* HasOp is monotone, and gains nothing for the typed kinds.
  <1>8. \A t, ty : ty \in {"begin", "body", "commit"} =>
          (HasOp(txnHistory', t, ty) <=> HasOp(txnHistory, t, ty))
    BY <1>4, <1>5 DEF HasOp
  <1>9. \A r \in runningTxns' : r \in runningTxns BY <1>1
  \* ---- uniqueness
  <1>11. \A o1, o2 \in Range(txnHistory') :
           o1.txnId = o2.txnId /\ o1.type = o2.type /\ o1.type \in {"begin", "body", "commit"}
             => o1 = o2
    BY <1>4, <1>5 DEF Inv
  \* ---- H1
  <1>12. \A ob, oc \in Range(txnHistory') :
           /\ ob.type = "begin" /\ oc.type = "commit" /\ ob.txnId = oc.txnId
           => ob.time < oc.time
    BY <1>4, <1>5 DEF Inv
  \* ---- commits have begin and body ops
  <1>13. \A oc \in Range(txnHistory') :
           oc.type = "commit" => HasOp(txnHistory', oc.txnId, "begin")
                              /\ HasOp(txnHistory', oc.txnId, "body")
    BY <1>4, <1>5, <1>8 DEF Inv
  \* ---- BodyOK
  <1>14. \A ob \in Range(txnHistory') : ob.type = "body" => BodyOK(ob)
    BY <1>4, <1>5 DEF Inv
  \* ---- updatedKeys
  <1>15. \A oc \in Range(txnHistory') :
           oc.type = "commit" =>
             oc.updatedKeys = {k \in Keys : WritesKey(txnHistory', oc.txnId, k)}
    BY <1>4, <1>5, <1>7 DEF Inv
  \* ---- H4
  <1>16. \A o1, o2 \in Range(txnHistory') :
           /\ o1.type = "commit" /\ o2.type = "commit" /\ o1.txnId # o2.txnId
           /\ o1.updatedKeys \cap o2.updatedKeys # {}
           => \/ \E b2 \in Range(txnHistory') :
                   b2.type = "begin" /\ b2.txnId = o2.txnId /\ o1.time =< b2.time
              \/ \E b1 \in Range(txnHistory') :
                   b1.type = "begin" /\ b1.txnId = o1.txnId /\ o2.time =< b1.time
    BY <1>4, <1>5 DEF Inv
  \* ---- running transactions
  <1>17. \A r \in runningTxns' :
           /\ r.id \in TxnIds
           /\ r.startTime \in 1..clock'
           /\ \E ob \in Range(txnHistory') :
                ob.type = "begin" /\ ob.txnId = r.id /\ ob.time = r.startTime
           /\ HasOp(txnHistory', r.id, "body")
           /\ ~HasOp(txnHistory', r.id, "commit")
    <2>1. SUFFICES ASSUME NEW r \in runningTxns'
                   PROVE  /\ r.id \in TxnIds
                          /\ r.startTime \in 1..clock'
                          /\ \E ob \in Range(txnHistory') :
                               ob.type = "begin" /\ ob.txnId = r.id /\ ob.time = r.startTime
                          /\ HasOp(txnHistory', r.id, "body")
                          /\ ~HasOp(txnHistory', r.id, "commit")
      OBVIOUS
    <2>2. r \in runningTxns BY <1>9, <2>1
    <2>3. /\ r.id \in TxnIds
          /\ r.startTime \in 1..clock
          /\ \E ob \in Range(txnHistory) :
               ob.type = "begin" /\ ob.txnId = r.id /\ ob.time = r.startTime
          /\ HasOp(txnHistory, r.id, "body")
          /\ ~HasOp(txnHistory, r.id, "commit")
      BY <2>2 DEF Inv
    <2>4. 1..clock \subseteq 1..clock' BY <1>1, <1>2
    <2>5. QED BY <2>3, <2>4, <1>4, <1>8
  <1>18. QED
    BY <1>3, <1>4, <1>6, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17 DEF Inv

----------------------------------------------------------------------------------------------------
(**************************************************************************************************)
(* Part 10.  StartAndRun.                                                                         *)
(*                                                                                                *)
(* Two ops are appended: a begin op and a body op, both carrying `tid`.  `Unused(tid)` says no    *)
(* operation in the history already mentions `tid`, which gives uniqueness, keeps the new begin    *)
(* op out of the H1 and H4 clauses (neither new op is a commit, and `tid` has no commit op), and  *)
(* keeps `tid`'s reads and writes from disturbing any existing commit op's `updatedKeys`.         *)
(**************************************************************************************************)

LEMMA UnusedMeans ==
  ASSUME NEW tid, Unused(tid)
  PROVE  \A op \in Range(txnHistory) : op.txnId # tid
PROOF
  BY DEF Unused

THEOREM StepStart ==
  ASSUME Inv, NEW tid \in TxnIds, NEW req \in Requests, StartAndRun(tid, req)
  PROVE  Inv'
PROOF
  <1> DEFINE prog == ProgramFor(tid, req, dataStore)
             ob0  == [type |-> "begin", txnId |-> tid, time |-> clock + 1]
             oy0  == [type |-> "body",  txnId |-> tid,
                      reads |-> prog.reads, writes |-> prog.writes]
  <1>1. /\ txnHistory' = txnHistory \o <<ob0, oy0>>
        /\ clock' = clock + 1
        /\ runningTxns' = runningTxns
                            \cup {[id |-> tid, startTime |-> clock + 1, commitTime |-> Empty]}
        /\ Unused(tid)
    BY DEF StartAndRun
  <1>2. clock \in Nat /\ IsSeq(txnHistory) BY DEF Inv
  <1>3. clock' \in Nat BY <1>1, <1>2
  <1>4. IsSeq(txnHistory') /\ Range(txnHistory') = Range(txnHistory) \cup {ob0, oy0}
    BY <1>1, <1>2, Append2IsSeq
  <1>5. \A op \in Range(txnHistory) : op.txnId # tid BY <1>1, UnusedMeans
  <1>6. /\ ob0.type = "begin" /\ ob0.txnId = tid /\ ob0.time = clock + 1
        /\ oy0.type = "body"  /\ oy0.txnId = tid
        /\ ob0 # oy0
    OBVIOUS
  \* No commit op carries tid, in either history.
  <1>7. \A op \in Range(txnHistory') : op.type = "commit" => op \in Range(txnHistory)
    BY <1>4, <1>6
  \* ---- shape and times
  <1>8. /\ \A op \in Range(txnHistory') : op.type \in OpTypes
        /\ \A op \in Range(txnHistory') :
             op.type \in {"begin", "commit"} => op.time \in 1..clock'
    <2>1. \A op \in Range(txnHistory) : op.type \in OpTypes BY DEF Inv
    <2>2. \A op \in Range(txnHistory) :
            op.type \in {"begin", "commit"} => op.time \in 1..clock
      BY DEF Inv
    <2>3. 1..clock \subseteq 1..clock' BY <1>1, <1>2
    <2>4. ob0.time \in 1..clock' BY <1>1, <1>2, <1>6
    <2>5. QED BY <1>4, <1>6, <2>1, <2>2, <2>3, <2>4 DEF OpTypes
  \* ---- uniqueness: the two new ops have a fresh txnId and differ in type.
  <1>9. \A o1, o2 \in Range(txnHistory') :
          o1.txnId = o2.txnId /\ o1.type = o2.type /\ o1.type \in {"begin", "body", "commit"}
            => o1 = o2
    <2>1. SUFFICES ASSUME NEW o1 \in Range(txnHistory'), NEW o2 \in Range(txnHistory'),
                          o1.txnId = o2.txnId, o1.type = o2.type,
                          o1.type \in {"begin", "body", "commit"}
                   PROVE  o1 = o2
      OBVIOUS
    <2>2. CASE o1 \in Range(txnHistory) /\ o2 \in Range(txnHistory)
      BY <2>1, <2>2 DEF Inv
    <2>3. CASE o1 \in {ob0, oy0} /\ o2 \in {ob0, oy0}
      BY <2>1, <2>3, <1>6
    <2>4. CASE o1 \in Range(txnHistory) /\ o2 \in {ob0, oy0}
      BY <2>1, <2>4, <1>5, <1>6
    <2>5. CASE o2 \in Range(txnHistory) /\ o1 \in {ob0, oy0}
      BY <2>1, <2>5, <1>5, <1>6
    <2>6. QED BY <1>4, <2>2, <2>3, <2>4, <2>5
  \* ---- H1: the new begin op has no matching commit op.
  <1>10. \A obb, occ \in Range(txnHistory') :
           /\ obb.type = "begin" /\ occ.type = "commit" /\ obb.txnId = occ.txnId
           => obb.time < occ.time
    <2>1. SUFFICES ASSUME NEW obb \in Range(txnHistory'), NEW occ \in Range(txnHistory'),
                          obb.type = "begin", occ.type = "commit", obb.txnId = occ.txnId
                   PROVE  obb.time < occ.time
      OBVIOUS
    <2>2. occ \in Range(txnHistory) BY <2>1, <1>7
    <2>3. occ.txnId # tid BY <2>2, <1>5
    <2>4. obb # ob0 BY <2>1, <2>3, <1>6
    <2>5. obb # oy0 BY <2>1, <1>6
    <2>6. obb \in Range(txnHistory) BY <2>1, <1>4, <2>4, <2>5
    <2>7. QED BY <2>1, <2>2, <2>6 DEF Inv
  \* ---- a commit op still has its begin and body ops (HasOp is monotone).
  <1>11. \A occ \in Range(txnHistory') :
           occ.type = "commit" => HasOp(txnHistory', occ.txnId, "begin")
                               /\ HasOp(txnHistory', occ.txnId, "body")
    <2>1. SUFFICES ASSUME NEW occ \in Range(txnHistory'), occ.type = "commit"
                   PROVE  HasOp(txnHistory', occ.txnId, "begin")
                          /\ HasOp(txnHistory', occ.txnId, "body")
      OBVIOUS
    <2>2. occ \in Range(txnHistory) BY <2>1, <1>7
    <2>3. HasOp(txnHistory, occ.txnId, "begin") /\ HasOp(txnHistory, occ.txnId, "body")
      BY <2>1, <2>2 DEF Inv
    <2>4. QED BY <2>3, <1>4 DEF HasOp
  \* ---- BodyOK: this is the workload lemma.
  <1>12. \A obb \in Range(txnHistory') : obb.type = "body" => BodyOK(obb)
    <2>1. SUFFICES ASSUME NEW obb \in Range(txnHistory'), obb.type = "body"
                   PROVE  BodyOK(obb)
      OBVIOUS
    <2>2. CASE obb \in Range(txnHistory)
      BY <2>1, <2>2 DEF Inv
    <2>3. CASE obb = oy0
      <3>1. BodyOK(prog) BY WorkloadSubsumed
      <3>2. oy0.reads = prog.reads /\ oy0.writes = prog.writes OBVIOUS
      <3>3. WriteKeysOf(oy0) = WriteKeysOf(prog) BY <3>2 DEF WriteKeysOf
      <3>4. QED BY <2>3, <3>1, <3>2, <3>3 DEF BodyOK
    <2>4. QED BY <1>4, <1>6, <2>1, <2>2, <2>3
  \* ---- updatedKeys: tid's writes cannot affect any existing commit op's record.
  <1>13. \A t, k : t # tid => (WritesKey(txnHistory', t, k) <=> WritesKey(txnHistory, t, k))
    BY <1>4, <1>6 DEF WritesKey
  <1>14. \A occ \in Range(txnHistory') :
           occ.type = "commit" =>
             occ.updatedKeys = {k \in Keys : WritesKey(txnHistory', occ.txnId, k)}
    <2>1. SUFFICES ASSUME NEW occ \in Range(txnHistory'), occ.type = "commit"
                   PROVE  occ.updatedKeys = {k \in Keys : WritesKey(txnHistory', occ.txnId, k)}
      OBVIOUS
    <2>2. occ \in Range(txnHistory) BY <2>1, <1>7
    <2>3. occ.txnId # tid BY <2>2, <1>5
    <2>4. occ.updatedKeys = {k \in Keys : WritesKey(txnHistory, occ.txnId, k)}
      BY <2>1, <2>2 DEF Inv
    <2>5. QED BY <2>4, <2>3, <1>13
  \* ---- H4: both commit ops are old, and their begin witnesses survive.
  <1>15. \A o1, o2 \in Range(txnHistory') :
           /\ o1.type = "commit" /\ o2.type = "commit" /\ o1.txnId # o2.txnId
           /\ o1.updatedKeys \cap o2.updatedKeys # {}
           => \/ \E b2 \in Range(txnHistory') :
                   b2.type = "begin" /\ b2.txnId = o2.txnId /\ o1.time =< b2.time
              \/ \E b1 \in Range(txnHistory') :
                   b1.type = "begin" /\ b1.txnId = o1.txnId /\ o2.time =< b1.time
    <2>1. SUFFICES ASSUME NEW o1 \in Range(txnHistory'), NEW o2 \in Range(txnHistory'),
                          o1.type = "commit", o2.type = "commit", o1.txnId # o2.txnId,
                          o1.updatedKeys \cap o2.updatedKeys # {}
                   PROVE  \/ \E b2 \in Range(txnHistory') :
                               b2.type = "begin" /\ b2.txnId = o2.txnId /\ o1.time =< b2.time
                          \/ \E b1 \in Range(txnHistory') :
                               b1.type = "begin" /\ b1.txnId = o1.txnId /\ o2.time =< b1.time
      OBVIOUS
    <2>2. o1 \in Range(txnHistory) /\ o2 \in Range(txnHistory) BY <2>1, <1>7
    <2>3. \/ \E b2 \in Range(txnHistory) :
                b2.type = "begin" /\ b2.txnId = o2.txnId /\ o1.time =< b2.time
          \/ \E b1 \in Range(txnHistory) :
                b1.type = "begin" /\ b1.txnId = o1.txnId /\ o2.time =< b1.time
      BY <2>1, <2>2 DEF Inv
    <2>4. QED BY <2>3, <1>4
  \* ---- running transactions: the old ones plus the new one, whose begin op was just appended.
  <1>16. \A r \in runningTxns' :
           /\ r.id \in TxnIds
           /\ r.startTime \in 1..clock'
           /\ \E obb \in Range(txnHistory') :
                obb.type = "begin" /\ obb.txnId = r.id /\ obb.time = r.startTime
           /\ HasOp(txnHistory', r.id, "body")
           /\ ~HasOp(txnHistory', r.id, "commit")
    <2>1. SUFFICES ASSUME NEW r \in runningTxns'
                   PROVE  /\ r.id \in TxnIds
                          /\ r.startTime \in 1..clock'
                          /\ \E obb \in Range(txnHistory') :
                               obb.type = "begin" /\ obb.txnId = r.id /\ obb.time = r.startTime
                          /\ HasOp(txnHistory', r.id, "body")
                          /\ ~HasOp(txnHistory', r.id, "commit")
      OBVIOUS
    <2>2. 1..clock \subseteq 1..clock' BY <1>1, <1>2
    <2>3. \A t : ~HasOp(txnHistory, t, "commit") => ~HasOp(txnHistory', t, "commit")
      BY <1>4, <1>6 DEF HasOp
    <2>4. CASE r \in runningTxns
      <3>1. /\ r.id \in TxnIds
            /\ r.startTime \in 1..clock
            /\ \E obb \in Range(txnHistory) :
                 obb.type = "begin" /\ obb.txnId = r.id /\ obb.time = r.startTime
            /\ HasOp(txnHistory, r.id, "body")
            /\ ~HasOp(txnHistory, r.id, "commit")
        BY <2>4 DEF Inv
      <3>1a. HasOp(txnHistory', r.id, "body") BY <3>1, <1>4 DEF HasOp
      <3>2. QED BY <3>1, <3>1a, <2>2, <2>3, <1>4
    <2>5. CASE r = [id |-> tid, startTime |-> clock + 1, commitTime |-> Empty]
      <3>1. r.id = tid /\ r.startTime = clock + 1 BY <2>5
      <3>2. r.startTime \in 1..clock' BY <3>1, <1>1, <1>2
      <3>3. ob0 \in Range(txnHistory')
            /\ ob0.type = "begin" /\ ob0.txnId = r.id /\ ob0.time = r.startTime
        BY <1>4, <1>6, <3>1
      <3>3a. HasOp(txnHistory', r.id, "body") BY <1>4, <1>6, <3>1 DEF HasOp
      <3>4. ~HasOp(txnHistory', tid, "commit")
        <4>1. SUFFICES ASSUME HasOp(txnHistory', tid, "commit") PROVE FALSE OBVIOUS
        <4>2. PICK x \in Range(txnHistory') : x.txnId = tid /\ x.type = "commit"
          BY <4>1 DEF HasOp
        <4>3. x \in Range(txnHistory) BY <4>2, <1>7
        <4>4. QED BY <4>2, <4>3, <1>5
      <3>5. QED BY <3>1, <3>2, <3>3, <3>3a, <3>4
    <2>6. QED BY <1>1, <2>1, <2>4, <2>5
  <1>17. QED
    BY <1>3, <1>4, <1>8, <1>9, <1>10, <1>11, <1>12, <1>14, <1>15, <1>16 DEF Inv

----------------------------------------------------------------------------------------------------
(**************************************************************************************************)
(* Part 11.  Commit.  The only action that grows the graph.                                       *)
(*                                                                                                *)
(* Two clauses need the action's guard rather than just its shape:                                *)
(*                                                                                                *)
(*   H1  the new commit op's time is clock+1, and `tid`'s begin op has time = startTime, which    *)
(*       `Inv` bounds by `clock`.                                                                 *)
(*   H4  `TxnCanCommit` is First-Committer-Wins: no commit op with time > startTime shares a key  *)
(*       with `tid`.  Contrapositive: a commit op sharing a key has time =< startTime, which is   *)
(*       `tid`'s begin time -- exactly the disjunct H4 asks for.                                  *)
(**************************************************************************************************)

\* A running transaction's begin time is pinned by its begin op, so all records for one id agree.
LEMMA RunningStartTime ==
  ASSUME Inv, NEW r1 \in runningTxns, NEW r2 \in runningTxns, r1.id = r2.id
  PROVE  r1.startTime = r2.startTime
PROOF
  <1>1. PICK b1 \in Range(txnHistory) :
          b1.type = "begin" /\ b1.txnId = r1.id /\ b1.time = r1.startTime
    BY DEF Inv
  <1>2. PICK b2 \in Range(txnHistory) :
          b2.type = "begin" /\ b2.txnId = r2.id /\ b2.time = r2.startTime
    BY DEF Inv
  <1>3. b1 = b2 BY <1>1, <1>2 DEF Inv
  <1>4. QED BY <1>1, <1>2, <1>3

THEOREM StepCommit ==
  ASSUME Inv, NEW tid, CommitTxn(tid)
  PROVE  Inv'
PROOF
  <1> DEFINE WK == KeysWrittenByTxn(tid, txnHistory)
             oc0 == [type |-> "commit", txnId |-> tid, time |-> clock + 1, updatedKeys |-> WK]
  <1>1. /\ txnHistory' = Append(txnHistory, oc0)
        /\ clock' = clock + 1
        /\ runningTxns' = {r \in runningTxns : r.id # tid}
        /\ TxnCanCommit(tid)
        /\ tid \in {txn.id : txn \in runningTxns}
    BY DEF CommitTxn
  <1>2. clock \in Nat /\ IsSeq(txnHistory) BY DEF Inv
  <1>3. clock' \in Nat BY <1>1, <1>2
  <1>4. IsSeq(txnHistory') /\ Range(txnHistory') = Range(txnHistory) \cup {oc0}
    BY <1>1, <1>2, AppendIsSeq
  <1>5. /\ oc0.type = "commit" /\ oc0.txnId = tid
        /\ oc0.time = clock + 1 /\ oc0.updatedKeys = WK
    OBVIOUS
  \* ---- The committing transaction: its running record, begin op and body op.
  <1>6. PICK r0 \in runningTxns :
          /\ r0.id = tid
          /\ ~\E op \in Range(txnHistory) :
                /\ op.type = "commit"
                /\ op.time > r0.startTime
                /\ WK \cap op.updatedKeys /= {}
    BY <1>1 DEF TxnCanCommit, KeysWrittenByTxn
  <1>7. PICK b0 \in Range(txnHistory) :
          b0.type = "begin" /\ b0.txnId = tid /\ b0.time = r0.startTime
    BY <1>6 DEF Inv
  <1>8. /\ r0.startTime \in 1..clock
        /\ HasOp(txnHistory, tid, "body")
        /\ ~HasOp(txnHistory, tid, "commit")
    BY <1>6 DEF Inv
  \* No commit op in the old history carries tid.
  <1>9. \A op \in Range(txnHistory) : op.type = "commit" => op.txnId # tid
    BY <1>8 DEF HasOp
  \* Appending a commit op changes neither reads nor writes.
  <1>10. /\ \A t, k : WritesKey(txnHistory', t, k) <=> WritesKey(txnHistory, t, k)
         /\ \A t, k : ReadsKey(txnHistory', t, k)  <=> ReadsKey(txnHistory, t, k)
    BY <1>1, <1>2, <1>5, RWSameAppend
  <1>11. WK = {k \in Keys : WritesKey(txnHistory, tid, k)}
    BY DEF KeysWrittenByTxn, WritesKey
  \* ---- shape and times
  <1>12. /\ \A op \in Range(txnHistory') : op.type \in OpTypes
         /\ \A op \in Range(txnHistory') :
              op.type \in {"begin", "commit"} => op.time \in 1..clock'
    <2>1. \A op \in Range(txnHistory) : op.type \in OpTypes BY DEF Inv
    <2>2. \A op \in Range(txnHistory) :
            op.type \in {"begin", "commit"} => op.time \in 1..clock
      BY DEF Inv
    <2>3. 1..clock \subseteq 1..clock' BY <1>1, <1>2
    <2>4. oc0.time \in 1..clock' BY <1>1, <1>2, <1>5
    <2>5. QED BY <1>4, <1>5, <2>1, <2>2, <2>3, <2>4 DEF OpTypes
  \* ---- uniqueness: tid had no commit op before.
  <1>13. \A o1, o2 \in Range(txnHistory') :
           o1.txnId = o2.txnId /\ o1.type = o2.type /\ o1.type \in {"begin", "body", "commit"}
             => o1 = o2
    <2>1. SUFFICES ASSUME NEW o1 \in Range(txnHistory'), NEW o2 \in Range(txnHistory'),
                          o1.txnId = o2.txnId, o1.type = o2.type,
                          o1.type \in {"begin", "body", "commit"}
                   PROVE  o1 = o2
      OBVIOUS
    <2>2. CASE o1 \in Range(txnHistory) /\ o2 \in Range(txnHistory)
      BY <2>1, <2>2 DEF Inv
    <2>3. CASE o1 = oc0 /\ o2 = oc0 BY <2>3
    <2>4. CASE o1 \in Range(txnHistory) /\ o2 = oc0
      BY <2>1, <2>4, <1>5, <1>9
    <2>5. CASE o2 \in Range(txnHistory) /\ o1 = oc0
      BY <2>1, <2>5, <1>5, <1>9
    <2>6. QED BY <1>4, <2>2, <2>3, <2>4, <2>5
  \* ---- H1: the new commit op against tid's begin op.
  <1>14. \A obb, occ \in Range(txnHistory') :
           /\ obb.type = "begin" /\ occ.type = "commit" /\ obb.txnId = occ.txnId
           => obb.time < occ.time
    <2>1. SUFFICES ASSUME NEW obb \in Range(txnHistory'), NEW occ \in Range(txnHistory'),
                          obb.type = "begin", occ.type = "commit", obb.txnId = occ.txnId
                   PROVE  obb.time < occ.time
      OBVIOUS
    <2>2. obb \in Range(txnHistory) BY <2>1, <1>4, <1>5
    <2>3. CASE occ \in Range(txnHistory)
      BY <2>1, <2>2, <2>3 DEF Inv
    <2>4. CASE occ = oc0
      <3>1. obb.txnId = tid BY <2>1, <2>4, <1>5
      <3>2. obb = b0 BY <2>1, <2>2, <3>1, <1>7 DEF Inv
      <3>3. obb.time = r0.startTime BY <3>2, <1>7
      <3>4. r0.startTime \in 1..clock BY <1>8
      <3>5. QED BY <2>4, <1>5, <3>3, <3>4, <1>2
    <2>5. QED BY <1>4, <2>1, <2>3, <2>4
  \* ---- the new commit op's begin and body ops are already there.
  <1>15. \A occ \in Range(txnHistory') :
           occ.type = "commit" => HasOp(txnHistory', occ.txnId, "begin")
                               /\ HasOp(txnHistory', occ.txnId, "body")
    <2>1. SUFFICES ASSUME NEW occ \in Range(txnHistory'), occ.type = "commit"
                   PROVE  HasOp(txnHistory', occ.txnId, "begin")
                          /\ HasOp(txnHistory', occ.txnId, "body")
      OBVIOUS
    <2>2. CASE occ \in Range(txnHistory)
      <3>1. HasOp(txnHistory, occ.txnId, "begin") /\ HasOp(txnHistory, occ.txnId, "body")
        BY <2>1, <2>2 DEF Inv
      <3>2. QED BY <3>1, <1>4 DEF HasOp
    <2>3. CASE occ = oc0
      <3>1. HasOp(txnHistory, tid, "begin") BY <1>7 DEF HasOp
      <3>2. HasOp(txnHistory, tid, "body") BY <1>8
      <3>3. QED BY <2>3, <1>5, <3>1, <3>2, <1>4 DEF HasOp
    <2>4. QED BY <1>4, <2>1, <2>2, <2>3
  \* ---- BodyOK: no new body op.
  <1>16. \A obb \in Range(txnHistory') : obb.type = "body" => BodyOK(obb)
    BY <1>4, <1>5 DEF Inv
  \* ---- updatedKeys: WK is by construction the set of keys tid wrote.
  <1>17. \A occ \in Range(txnHistory') :
           occ.type = "commit" =>
             occ.updatedKeys = {k \in Keys : WritesKey(txnHistory', occ.txnId, k)}
    <2>1. SUFFICES ASSUME NEW occ \in Range(txnHistory'), occ.type = "commit"
                   PROVE  occ.updatedKeys = {k \in Keys : WritesKey(txnHistory', occ.txnId, k)}
      OBVIOUS
    <2>2. CASE occ \in Range(txnHistory)
      <3>1. occ.updatedKeys = {k \in Keys : WritesKey(txnHistory, occ.txnId, k)}
        BY <2>1, <2>2 DEF Inv
      <3>2. QED BY <3>1, <1>10
    <2>3. CASE occ = oc0
      BY <2>3, <1>5, <1>11, <1>10
    <2>4. QED BY <1>4, <2>1, <2>2, <2>3
  \* ---- H4: First-Committer-Wins.
  <1>18. \A o1, o2 \in Range(txnHistory') :
           /\ o1.type = "commit" /\ o2.type = "commit" /\ o1.txnId # o2.txnId
           /\ o1.updatedKeys \cap o2.updatedKeys # {}
           => \/ \E b2 \in Range(txnHistory') :
                   b2.type = "begin" /\ b2.txnId = o2.txnId /\ o1.time =< b2.time
              \/ \E b1 \in Range(txnHistory') :
                   b1.type = "begin" /\ b1.txnId = o1.txnId /\ o2.time =< b1.time
    <2>1. SUFFICES ASSUME NEW o1 \in Range(txnHistory'), NEW o2 \in Range(txnHistory'),
                          o1.type = "commit", o2.type = "commit", o1.txnId # o2.txnId,
                          o1.updatedKeys \cap o2.updatedKeys # {}
                   PROVE  \/ \E b2 \in Range(txnHistory') :
                               b2.type = "begin" /\ b2.txnId = o2.txnId /\ o1.time =< b2.time
                          \/ \E b1 \in Range(txnHistory') :
                               b1.type = "begin" /\ b1.txnId = o1.txnId /\ o2.time =< b1.time
      OBVIOUS
    \* The key step, stated once and used for both orientations.
    <2>2. ASSUME NEW op \in Range(txnHistory), op.type = "commit",
                 WK \cap op.updatedKeys # {}
          PROVE  op.time =< b0.time
      <3>1. ~(op.time > r0.startTime) BY <1>6, <2>2
      <3>2. op.time \in 1..clock BY <2>2 DEF Inv
      <3>3. r0.startTime \in 1..clock BY <1>8
      <3>4. QED BY <3>1, <3>2, <3>3, <1>2, <1>7
    <2>3. CASE o1 \in Range(txnHistory) /\ o2 \in Range(txnHistory)
      <3>1. \/ \E b2 \in Range(txnHistory) :
                  b2.type = "begin" /\ b2.txnId = o2.txnId /\ o1.time =< b2.time
            \/ \E b1 \in Range(txnHistory) :
                  b1.type = "begin" /\ b1.txnId = o1.txnId /\ o2.time =< b1.time
        BY <2>1, <2>3 DEF Inv
      <3>2. QED BY <3>1, <1>4
    <2>4. CASE o1 \in Range(txnHistory) /\ o2 = oc0
      \* o1 committed before tid began.
      <3>1. o2.updatedKeys = WK BY <2>4, <1>5
      <3>2. WK \cap o1.updatedKeys # {} BY <2>1, <3>1
      <3>3. o1.time =< b0.time BY <2>2, <2>1, <2>4, <3>2
      <3>4. b0 \in Range(txnHistory') /\ b0.type = "begin" /\ b0.txnId = o2.txnId
        BY <1>7, <1>4, <2>4, <1>5
      <3>5. QED BY <3>3, <3>4
    <2>5. CASE o2 \in Range(txnHistory) /\ o1 = oc0
      <3>1. o1.updatedKeys = WK BY <2>5, <1>5
      <3>2. WK \cap o2.updatedKeys # {} BY <2>1, <3>1
      <3>3. o2.time =< b0.time BY <2>2, <2>1, <2>5, <3>2
      <3>4. b0 \in Range(txnHistory') /\ b0.type = "begin" /\ b0.txnId = o1.txnId
        BY <1>7, <1>4, <2>5, <1>5
      <3>5. QED BY <3>3, <3>4
    <2>6. CASE o1 = oc0 /\ o2 = oc0 BY <2>1, <2>6
    <2>7. QED BY <1>4, <2>3, <2>4, <2>5, <2>6
  \* ---- running transactions: tid is removed; the rest keep their witnesses.
  <1>19. \A r \in runningTxns' :
           /\ r.id \in TxnIds
           /\ r.startTime \in 1..clock'
           /\ \E obb \in Range(txnHistory') :
                obb.type = "begin" /\ obb.txnId = r.id /\ obb.time = r.startTime
           /\ HasOp(txnHistory', r.id, "body")
           /\ ~HasOp(txnHistory', r.id, "commit")
    <2>1. SUFFICES ASSUME NEW r \in runningTxns'
                   PROVE  /\ r.id \in TxnIds
                          /\ r.startTime \in 1..clock'
                          /\ \E obb \in Range(txnHistory') :
                               obb.type = "begin" /\ obb.txnId = r.id /\ obb.time = r.startTime
                          /\ HasOp(txnHistory', r.id, "body")
                          /\ ~HasOp(txnHistory', r.id, "commit")
      OBVIOUS
    <2>2. r \in runningTxns /\ r.id # tid BY <1>1, <2>1
    <2>3. /\ r.id \in TxnIds
          /\ r.startTime \in 1..clock
          /\ \E obb \in Range(txnHistory) :
               obb.type = "begin" /\ obb.txnId = r.id /\ obb.time = r.startTime
          /\ HasOp(txnHistory, r.id, "body")
          /\ ~HasOp(txnHistory, r.id, "commit")
      BY <2>2 DEF Inv
    <2>4. 1..clock \subseteq 1..clock' BY <1>1, <1>2
    <2>5. HasOp(txnHistory', r.id, "body") BY <2>3, <1>4 DEF HasOp
    <2>6. ~HasOp(txnHistory', r.id, "commit")
      <3>1. SUFFICES ASSUME HasOp(txnHistory', r.id, "commit") PROVE FALSE OBVIOUS
      <3>2. PICK x \in Range(txnHistory') : x.txnId = r.id /\ x.type = "commit"
        BY <3>1 DEF HasOp
      <3>3. x # oc0 BY <3>2, <1>5, <2>2
      <3>4. x \in Range(txnHistory) BY <3>2, <3>3, <1>4
      <3>5. QED BY <3>2, <3>4, <2>3 DEF HasOp
    <2>7. QED BY <2>3, <2>4, <2>5, <2>6, <1>4
  <1>20. QED
    BY <1>3, <1>4, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, <1>19 DEF Inv

----------------------------------------------------------------------------------------------------
(**************************************************************************************************)
(* Part 12.  Assembly.                                                                            *)
(**************************************************************************************************)

THEOREM StepStutter ==
  ASSUME Inv, UNCHANGED vars
  PROVE  Inv'
PROOF
  <1>1. /\ clock' = clock
        /\ runningTxns' = runningTxns
        /\ txnHistory' = txnHistory
    BY DEF vars
  <1>2. QED BY <1>1 DEF Inv

THEOREM Inductive == Inv /\ [Next]_vars => Inv'
PROOF
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv' OBVIOUS
  <1>1. CASE UNCHANGED vars BY <1>1, StepStutter
  <1>2. CASE Next
    <2>1. CASE \E tid \in TxnIds, req \in Requests : StartAndRun(tid, req)
      BY <2>1, StepStart
    <2>2. CASE \E tid \in TxnIds : CommitTxn(tid)
      BY <2>2, StepCommit
    <2>3. CASE \E tid \in TxnIds : AbortTxn(tid)
      BY <2>3, StepAbort
    <2>4. CASE AllTxnsDone /\ UNCHANGED vars
      BY <2>4, StepStutter
    <2>5. QED BY <1>2, <2>1, <2>2, <2>3, <2>4 DEF Next
  <1>3. QED BY <1>1, <1>2

(**************************************************************************************************)
(* The top-level theorem.                                                                         *)
(**************************************************************************************************)

THEOREM Safety == Spec => []SerializableViaPath
PROOF
  <1>1. Init => Inv BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv' BY Inductive
  <1>3. Inv => SerializableViaPath BY InvImpliesSerializable
  <1>4. Spec => []Inv
    BY <1>1, <1>2, PTL DEF Spec
  <1>5. QED BY <1>3, <1>4, PTL

====================================================================================================
