----------------------------- MODULE TPCC_Proofs -----------------------------
(*****************************************************************************)
(* TLAPS proof that every history of the New-Order + Payment + Stock-Level   *)
(* mix is conflict serializable under column-granularity SI:                 *)
(*                                                                           *)
(*     THEOREM Safety == Spec => []SerializableViaPath                       *)
(*                                                                           *)
(* The argument is a rank function on the multi-version serialization graph. *)
(* Updaters are ranked by commit time, read-only transactions by begin time: *)
(*                                                                           *)
(*     rank(t) == IF t writes anything THEN commit(t) ELSE begin(t)          *)
(*                                                                           *)
(* Three history facts make every MVSG edge strictly increase this rank:     *)
(*                                                                           *)
(*   H1  begin(t) < commit(t)                                                *)
(*   H2  an updater that reads a key someone writes also writes that key     *)
(*   H3  two committed writers of a common key have disjoint lifetimes (FCW) *)
(*                                                                           *)
(* H2 is the workload fact.  Payment writes every key it reads.  Stock-Level *)
(* writes nothing.  New-Order reads four columns it does not write -- W_TAX, *)
(* D_TAX, C_DISCOUNT/C_LAST, I_PRICE -- and those columns are never written  *)
(* by this mix, so they cannot appear on an rw-edge.  The keys New-Order     *)
(* both reads and someone may write (D_NEXT_O_ID, S_QUANTITY) it also writes.*)
(*                                                                           *)
(* Column granularity is essential: at row granularity New-Order and Payment *)
(* share the WAREHOUSE and DISTRICT rows, manufacturing false ww/rw edges    *)
(* that close a cycle.                                                       *)
(*****************************************************************************)

EXTENDS TPCC, NaturalsInduction, SequenceTheorems, FiniteSetTheorems, TLAPS

ASSUME RobustMix == EnabledTxnTypes \subseteq {"NewOrder", "Payment", "StockLevel"}
ASSUME ColumnMode == ColumnGranularity = TRUE

ASSUME NumWarehousesNat == NumWarehouses \in Nat
ASSUME NumDistrictsNat  == NumDistricts \in Nat
ASSUME NumCustomersNat  == NumCustomers \in Nat
ASSUME NumItemsNat      == NumItems \in Nat
ASSUME MaxOrdersNat     == MaxOrders \in Nat
ASSUME InitOrdersNat    == InitOrders \in Nat
ASSUME StockLevelDepthNat == StockLevelDepth \in Nat
ASSUME NumTxnsNat       == NumTxns \in Nat

-----------------------------------------------------------------------------
(*****************************************************************************)
(* 1.  Empty history                                                         *)
(*****************************************************************************)

LEMMA RangeEq == \A f : Range(f) = SI!Range(f)
BY DEF Range, SI!Range

LEMMA EmptyRange == Range(<<>>) = {}
<1>1. <<>> \in Seq({})
  BY EmptySeq
<1>2. Range(<<>>) = {<<>>[i] : i \in 1..0}
  BY <1>1, RangeEquality
<1>. QED
  BY <1>2

LEMMA EmptyCommitted == SI!CommittedTxns(<<>>) = {}
<1>1. SI!Range(<<>>) = {}
  BY EmptyRange, RangeEq
<1>2. {op \in SI!Range(<<>>) : op.type = "commit"} = {}
  BY <1>1
<1>. QED
  BY <1>1, <1>2 DEF SI!CommittedTxns

LEMMA EmptyGraph == SI!SerializationGraph(<<>>) = {}
<1>1. SI!CommittedTxns(<<>>) = {}
  BY EmptyCommitted
<1>. QED
  BY <1>1 DEF SI!SerializationGraph

LEMMA EmptyGraphNodes == SI!GraphNodes({}) = {}
BY DEF SI!GraphNodes

LEMMA FunEmptyCodomain ==
  ASSUME NEW S, S # {}
  PROVE  [S -> {}] = {}
<1> SUFFICES ASSUME NEW f \in [S -> {}]
             PROVE  FALSE
  OBVIOUS
<1>1. PICK x \in S : TRUE
  OBVIOUS
<1>2. f[x] \in {}
  OBVIOUS
<1>. QED
  BY <1>2

LEMMA PathConsecutive ==
  ASSUME NEW edges, NEW p \in SI!Paths(edges)
  PROVE  \A i \in 1..(Len(p)-1) : <<p[i], p[i+1]>> \in edges
BY DEF SI!Paths

-----------------------------------------------------------------------------
(*****************************************************************************)
(* 2.  Rank along a path implies acyclicity                                  *)
(*****************************************************************************)

LEMMA RankAlongSeq ==
  ASSUME NEW n \in Nat,
         NEW r(_),
         NEW p,
         n >= 1,
         \A i \in 1..n : r(p[i]) \in Nat /\ r(p[i+1]) \in Nat /\ r(p[i]) < r(p[i+1])
  PROVE  r(p[1]) + n <= r(p[n+1])
<1> DEFINE P(m) ==
             m \in Nat /\ m >= 1 /\
             (\A i \in 1..m : r(p[i]) \in Nat /\ r(p[i+1]) \in Nat /\ r(p[i]) < r(p[i+1]))
             => r(p[1]) + m <= r(p[m+1])
<1>1. P(1)
  OBVIOUS
<1>2. \A m \in Nat : P(m) => P(m+1)
  <2> SUFFICES ASSUME NEW m \in Nat, P(m)
               PROVE  P(m+1)
    OBVIOUS
  <2>1. SUFFICES ASSUME m+1 >= 1,
                        \A i \in 1..(m+1) : r(p[i]) \in Nat /\ r(p[i+1]) \in Nat /\ r(p[i]) < r(p[i+1])
                 PROVE  r(p[1]) + (m+1) <= r(p[(m+1)+1])
    OBVIOUS
  <2>2. CASE m = 0
    BY <2>1, <2>2
  <2>3. CASE m >= 1
    <3>1. r(p[1]) + m <= r(p[m+1])
      BY <2>1, <2>3
    <3>2. r(p[m+1]) \in Nat /\ r(p[m+2]) \in Nat /\ r(p[m+1]) < r(p[m+2])
      BY <2>1
    <3>. QED
      BY <3>1, <3>2
  <2>. QED
    BY <2>2, <2>3
<1>3. \A m \in Nat : P(m)
  BY <1>1, <1>2, NatInduction
<1>. QED
  BY <1>3

LEMMA PathProperties ==
  ASSUME NEW edges, NEW p \in SI!Paths(edges)
  PROVE  /\ p \in Seq(SI!GraphNodes(edges))
         /\ Len(p) \in Nat
         /\ Len(p) >= 1
         /\ \A i \in 1..(Len(p)-1) : <<p[i], p[i+1]>> \in edges
<1> DEFINE nodes == SI!GraphNodes(edges)
           maxLen == SI!PathBound(edges)
<1>1. p \in UNION {[1..n -> nodes] : n \in 1..maxLen}
      /\ \A i \in 1..(Len(p)-1) : <<p[i], p[i+1]>> \in edges
  BY DEF SI!Paths
<1>2. PICK n \in 1..maxLen : p \in [1..n -> nodes]
  BY <1>1
<1>3. n \in Nat /\ n >= 1
  BY <1>2 DEF SI!PathBound
<1>4. p \in Seq(nodes)
  BY <1>2, <1>3
<1>5. Len(p) = n
  BY <1>2, <1>4, LenProperties
<1>. QED
  BY <1>1, <1>4, <1>5, <1>3

LEMMA EmptyNoCycle == ~SI!IsCycleViaPath({})
<1> SUFFICES ASSUME SI!IsCycleViaPath({})
             PROVE  FALSE
  OBVIOUS
<1>1. PICK p \in SI!Paths({}) : Len(p) > 1 /\ p[1] = p[Len(p)]
  BY DEF SI!IsCycleViaPath
<1>2. Len(p) \in Nat
  BY <1>1, PathProperties
<1>3. 1 \in 1..(Len(p)-1)
  BY <1>1, <1>2
<1>4. <<p[1], p[2]>> \in {}
  BY <1>1, <1>3, PathConsecutive
<1>. QED
  BY <1>4

LEMMA EmptySerializable == SI!IsConflictSerializableViaPath(<<>>)
BY EmptyGraph, EmptyNoCycle DEF SI!IsConflictSerializableViaPath

LEMMA RankedNoCycle ==
  ASSUME NEW edges,
         NEW r(_),
         \A e \in edges : r(e[1]) \in Nat /\ r(e[2]) \in Nat /\ r(e[1]) < r(e[2])
  PROVE  ~SI!IsCycleViaPath(edges)
<1> SUFFICES ASSUME SI!IsCycleViaPath(edges)
             PROVE  FALSE
  OBVIOUS
<1>1. PICK p \in SI!Paths(edges) : Len(p) > 1 /\ p[1] = p[Len(p)]
  BY DEF SI!IsCycleViaPath
<1>2. p \in Seq(SI!GraphNodes(edges))
      /\ Len(p) \in Nat
      /\ Len(p) >= 1
      /\ \A i \in 1..(Len(p)-1) : <<p[i], p[i+1]>> \in edges
  BY <1>1, PathProperties
<1>3. Len(p) - 1 \in Nat /\ Len(p) - 1 >= 1
  BY <1>1, <1>2
<1>4. \A i \in 1..(Len(p)-1) :
         r(p[i]) \in Nat /\ r(p[i+1]) \in Nat /\ r(p[i]) < r(p[i+1])
  <2> SUFFICES ASSUME NEW i \in 1..(Len(p)-1)
               PROVE  r(p[i]) \in Nat /\ r(p[i+1]) \in Nat /\ r(p[i]) < r(p[i+1])
    OBVIOUS
  <2>1. <<p[i], p[i+1]>> \in edges
    BY <1>2
  <2>. QED
    BY <2>1
<1>5. r(p[1]) + (Len(p)-1) <= r(p[(Len(p)-1)+1])
  BY <1>3, <1>4, RankAlongSeq
<1>6. (Len(p)-1)+1 = Len(p)
  BY <1>2, <1>3
<1>7. r(p[1]) + (Len(p)-1) <= r(p[Len(p)])
  BY <1>5, <1>6
<1>8. r(p[1]) \in Nat
  BY <1>1, <1>3, <1>4
<1>9. r(p[1]) = r(p[Len(p)])
  BY <1>1
<1>. QED
  BY <1>3, <1>7, <1>8, <1>9

-----------------------------------------------------------------------------
(*****************************************************************************)
(* 3.  History facts H1--H3 and the rank                                     *)
(*****************************************************************************)

UniqueBegin(h) ==
  \A op1, op2 \in Range(h) :
    op1.type = "begin" /\ op2.type = "begin" /\ op1.txnId = op2.txnId => op1 = op2

UniqueCommit(h) ==
  \A op1, op2 \in Range(h) :
    op1.type = "commit" /\ op2.type = "commit" /\ op1.txnId = op2.txnId => op1 = op2

UniqueBody(h) ==
  \A op1, op2 \in Range(h) :
    op1.type = "body" /\ op2.type = "body" /\ op1.txnId = op2.txnId => op1 = op2

TimedOpsOK(h) ==
  \A op \in Range(h) :
    op.type \in {"begin", "commit"} => "time" \in DOMAIN op /\ op.time \in Nat

CommittedOK(h) ==
  \A t \in SI!CommittedTxns(h) :
    /\ \E b \in Range(h) : b.type = "begin" /\ b.txnId = t
    /\ \E c \in Range(h) : c.type = "commit" /\ c.txnId = t

H1(h) ==
  \A b, c \in Range(h) :
    b.type = "begin" /\ c.type = "commit" /\ b.txnId = c.txnId => b.time < c.time

\* An updater that reads a key which some committed transaction writes
\* must itself write that key.  Read-only columns of this mix (W_TAX, D_TAX,
\* CUST.info, ITEM.info) are never written, so they are exempt.
ReadOnlyCol(k) ==
  /\ "tbl" \in DOMAIN k
  /\ "col" \in DOMAIN k
  /\ \/ /\ k.tbl = "WH"   /\ k.col = "tax"
     \/ /\ k.tbl = "DIST" /\ k.col = "tax"
     \/ /\ k.tbl = "CUST" /\ k.col = "info"
     \/ /\ k.tbl = "ITEM" /\ k.col = "info"

H2(h) ==
  \A t \in SI!CommittedTxns(h) :
    SI!KeysWrittenByTxn(h, t) # {} =>
      \A k \in Keys :
        SI!ReadsKey(h, t, k) /\ (\E t2 \in SI!CommittedTxns(h) : SI!WritesKey(h, t2, k))
          => SI!WritesKey(h, t, k)

H3(h) ==
  \A t1, t2 \in SI!CommittedTxns(h) :
    /\ t1 # t2
    /\ SI!KeysWrittenByTxn(h, t1) \cap SI!KeysWrittenByTxn(h, t2) # {}
    =>
    \A b1, c1, b2, c2 \in Range(h) :
      /\ b1.type = "begin"  /\ b1.txnId = t1
      /\ c1.type = "commit" /\ c1.txnId = t1
      /\ b2.type = "begin"  /\ b2.txnId = t2
      /\ c2.type = "commit" /\ c2.txnId = t2
      => c1.time < b2.time \/ c2.time < b1.time

HistFacts(h) ==
  /\ UniqueBegin(h)
  /\ UniqueCommit(h)
  /\ UniqueBody(h)
  /\ TimedOpsOK(h)
  /\ CommittedOK(h)
  /\ H1(h)
  /\ H2(h)
  /\ H3(h)

Rank(h, t) ==
  IF SI!KeysWrittenByTxn(h, t) # {}
  THEN SI!CommitOp(h, t).time
  ELSE SI!BeginOp(h, t).time

LEMMA ChooseExists ==
  ASSUME NEW S, NEW P(_), \E x \in S : P(x)
  PROVE  P(CHOOSE x \in S : P(x))
<1>1. PICK y \in S : P(y)
  OBVIOUS
<1>. QED
  OBVIOUS

LEMMA ChooseBegin ==
  ASSUME NEW h, NEW t,
         \E b \in Range(h) : b.type = "begin" /\ b.txnId = t
  PROVE  SI!BeginOp(h, t) \in Range(h)
         /\ SI!BeginOp(h, t).type = "begin"
         /\ SI!BeginOp(h, t).txnId = t
<1> DEFINE P(op) == op.type = "begin" /\ op.txnId = t
<1>1. P(CHOOSE op \in Range(h) : P(op))
  BY ChooseExists
<1>. QED
  BY <1>1, RangeEq DEF SI!BeginOp

LEMMA ChooseCommit ==
  ASSUME NEW h, NEW t,
         \E c \in Range(h) : c.type = "commit" /\ c.txnId = t
  PROVE  SI!CommitOp(h, t) \in Range(h)
         /\ SI!CommitOp(h, t).type = "commit"
         /\ SI!CommitOp(h, t).txnId = t
<1> DEFINE P(op) == op.type = "commit" /\ op.txnId = t
<1>1. P(CHOOSE op \in Range(h) : P(op))
  BY ChooseExists
<1>. QED
  BY <1>1, RangeEq DEF SI!CommitOp

LEMMA BeginOpUnique ==
  ASSUME NEW h, NEW t, UniqueBegin(h),
         NEW b \in Range(h), b.type = "begin", b.txnId = t
  PROVE  SI!BeginOp(h, t) = b
<1>1. SI!BeginOp(h, t) \in Range(h)
      /\ SI!BeginOp(h, t).type = "begin"
      /\ SI!BeginOp(h, t).txnId = t
  BY ChooseBegin
<1>. QED
  BY <1>1 DEF UniqueBegin

LEMMA CommitOpUnique ==
  ASSUME NEW h, NEW t, UniqueCommit(h),
         NEW c \in Range(h), c.type = "commit", c.txnId = t
  PROVE  SI!CommitOp(h, t) = c
<1>1. SI!CommitOp(h, t) \in Range(h)
      /\ SI!CommitOp(h, t).type = "commit"
      /\ SI!CommitOp(h, t).txnId = t
  BY ChooseCommit
<1>. QED
  BY <1>1 DEF UniqueCommit

LEMMA RankType ==
  ASSUME NEW h, NEW t \in SI!CommittedTxns(h), HistFacts(h)
  PROVE  Rank(h, t) \in Nat
<1>1. \E b \in Range(h) : b.type = "begin" /\ b.txnId = t
      /\ \E c \in Range(h) : c.type = "commit" /\ c.txnId = t
  BY DEF HistFacts, CommittedOK
<1>2. SI!BeginOp(h, t) \in Range(h) /\ SI!BeginOp(h, t).type = "begin"
  BY <1>1, ChooseBegin
<1>3. SI!CommitOp(h, t) \in Range(h) /\ SI!CommitOp(h, t).type = "commit"
  BY <1>1, ChooseCommit
<1>4. SI!BeginOp(h, t).time \in Nat
  BY <1>2 DEF HistFacts, TimedOpsOK
<1>5. SI!CommitOp(h, t).time \in Nat
  BY <1>3 DEF HistFacts, TimedOpsOK
<1>. QED
  BY <1>4, <1>5 DEF Rank

LEMMA BeginTimeType ==
  ASSUME NEW h, NEW t \in SI!CommittedTxns(h), HistFacts(h)
  PROVE  SI!BeginOp(h, t).time \in Nat
<1>1. \E b \in Range(h) : b.type = "begin" /\ b.txnId = t
  BY DEF HistFacts, CommittedOK
<1>2. SI!BeginOp(h, t) \in Range(h) /\ SI!BeginOp(h, t).type = "begin"
  BY <1>1, ChooseBegin
<1>. QED
  BY <1>2 DEF HistFacts, TimedOpsOK

LEMMA CommitTimeType ==
  ASSUME NEW h, NEW t \in SI!CommittedTxns(h), HistFacts(h)
  PROVE  SI!CommitOp(h, t).time \in Nat
<1>1. \E c \in Range(h) : c.type = "commit" /\ c.txnId = t
  BY DEF HistFacts, CommittedOK
<1>2. SI!CommitOp(h, t) \in Range(h) /\ SI!CommitOp(h, t).type = "commit"
  BY <1>1, ChooseCommit
<1>. QED
  BY <1>2 DEF HistFacts, TimedOpsOK

LEMMA WroteMeansNonempty ==
  ASSUME NEW h, NEW t, NEW k \in Keys,
         SI!WritesKey(h, t, k)
  PROVE  SI!KeysWrittenByTxn(h, t) # {}
BY DEF SI!KeysWrittenByTxn, SI!WritesKey

LEMMA WWEdgesRank ==
  ASSUME NEW h, HistFacts(h),
         NEW t1 \in SI!CommittedTxns(h), NEW t2 \in SI!CommittedTxns(h),
         t1 # t2,
         SI!WWDependency(h, t1, t2)
  PROVE  Rank(h, t1) \in Nat /\ Rank(h, t2) \in Nat /\ Rank(h, t1) < Rank(h, t2)
<1>1. PICK k \in Keys : SI!WritesKey(h, t1, k) /\ SI!WritesKey(h, t2, k)
  BY DEF SI!WWDependency
<1>2. SI!CommitOp(h, t1).time < SI!CommitOp(h, t2).time
  BY DEF SI!WWDependency
<1>3. SI!KeysWrittenByTxn(h, t1) # {}
  BY <1>1, WroteMeansNonempty
<1>4. SI!KeysWrittenByTxn(h, t2) # {}
  BY <1>1, WroteMeansNonempty
<1>5. Rank(h, t1) = SI!CommitOp(h, t1).time
  BY <1>3 DEF Rank
<1>6. Rank(h, t2) = SI!CommitOp(h, t2).time
  BY <1>4 DEF Rank
<1>7. Rank(h, t1) \in Nat
  BY RankType
<1>8. Rank(h, t2) \in Nat
  BY RankType
<1>. QED
  BY <1>2, <1>5, <1>6, <1>7, <1>8

LEMMA WREdgesRank ==
  ASSUME NEW h, HistFacts(h),
         NEW t1 \in SI!CommittedTxns(h), NEW t2 \in SI!CommittedTxns(h),
         t1 # t2,
         SI!WRDependency(h, t1, t2)
  PROVE  Rank(h, t1) \in Nat /\ Rank(h, t2) \in Nat /\ Rank(h, t1) < Rank(h, t2)
<1>1. PICK k \in Keys : SI!WritesKey(h, t1, k) /\ SI!ReadsKey(h, t2, k)
  BY DEF SI!WRDependency
<1>2. SI!CommitOp(h, t1).time < SI!BeginOp(h, t2).time
  BY DEF SI!WRDependency
<1>3. SI!KeysWrittenByTxn(h, t1) # {}
  BY <1>1, WroteMeansNonempty
<1>4. Rank(h, t1) = SI!CommitOp(h, t1).time
  BY <1>3 DEF Rank
<1>5. Rank(h, t1) \in Nat
  BY RankType
<1>6. SI!CommitOp(h, t1).time \in Nat
  BY CommitTimeType
<1>7. SI!BeginOp(h, t2).time \in Nat
  BY BeginTimeType
<1>8. CASE SI!KeysWrittenByTxn(h, t2) = {}
  <2>1. Rank(h, t2) = SI!BeginOp(h, t2).time
    BY <1>8 DEF Rank
  <2>2. Rank(h, t2) \in Nat
    BY <1>7, <2>1
  <2>. QED
    BY <1>2, <1>4, <1>5, <2>1, <2>2
<1>9. CASE SI!KeysWrittenByTxn(h, t2) # {}
  <2>1. Rank(h, t2) = SI!CommitOp(h, t2).time
    BY <1>9 DEF Rank
  <2>2. Rank(h, t2) \in Nat
    BY RankType
  <2>3. \E b \in Range(h) : b.type = "begin" /\ b.txnId = t2
        /\ \E c \in Range(h) : c.type = "commit" /\ c.txnId = t2
    BY DEF HistFacts, CommittedOK
  <2>4. SI!BeginOp(h, t2).time < SI!CommitOp(h, t2).time
    BY <2>3, ChooseBegin, ChooseCommit DEF HistFacts, H1
  <2>. QED
    BY <1>2, <1>4, <1>5, <1>6, <1>7, <2>1, <2>2, <2>4
<1>. QED
  BY <1>8, <1>9

LEMMA RWEdgesRank ==
  ASSUME NEW h, HistFacts(h),
         NEW t1 \in SI!CommittedTxns(h), NEW t2 \in SI!CommittedTxns(h),
         t1 # t2,
         SI!RWDependency(h, t1, t2)
  PROVE  Rank(h, t1) \in Nat /\ Rank(h, t2) \in Nat /\ Rank(h, t1) < Rank(h, t2)
<1>1. PICK k \in Keys : SI!ReadsKey(h, t1, k) /\ SI!WritesKey(h, t2, k)
  BY DEF SI!RWDependency
<1>2. SI!BeginOp(h, t1).time < SI!CommitOp(h, t2).time
  BY DEF SI!RWDependency
<1>3. SI!KeysWrittenByTxn(h, t2) # {}
  BY <1>1, WroteMeansNonempty
<1>4. Rank(h, t2) = SI!CommitOp(h, t2).time
  BY <1>3 DEF Rank
<1>5. Rank(h, t2) \in Nat
  BY RankType
<1>6. SI!BeginOp(h, t1).time \in Nat
  BY BeginTimeType
<1>7. SI!CommitOp(h, t2).time \in Nat
  BY CommitTimeType
<1>8. CASE SI!KeysWrittenByTxn(h, t1) = {}
  <2>1. Rank(h, t1) = SI!BeginOp(h, t1).time
    BY <1>8 DEF Rank
  <2>. QED
    BY <1>2, <1>4, <1>5, <1>6, <2>1
<1>9. CASE SI!KeysWrittenByTxn(h, t1) # {}
  <2>1. Rank(h, t1) = SI!CommitOp(h, t1).time
    BY <1>9 DEF Rank
  <2>2. Rank(h, t1) \in Nat
    BY RankType
  <2>3. SI!WritesKey(h, t1, k)
    BY <1>1, <1>3, <1>9 DEF HistFacts, H2
  <2>4. k \in SI!KeysWrittenByTxn(h, t1) \cap SI!KeysWrittenByTxn(h, t2)
    BY <1>1, <1>3, <2>3, WroteMeansNonempty DEF SI!KeysWrittenByTxn
  <2>5. SI!KeysWrittenByTxn(h, t1) \cap SI!KeysWrittenByTxn(h, t2) # {}
    BY <2>4
  <2>6. \E b1 \in Range(h) : b1.type = "begin" /\ b1.txnId = t1
        /\ \E c1 \in Range(h) : c1.type = "commit" /\ c1.txnId = t1
        /\ \E b2 \in Range(h) : b2.type = "begin" /\ b2.txnId = t2
        /\ \E c2 \in Range(h) : c2.type = "commit" /\ c2.txnId = t2
    BY DEF HistFacts, CommittedOK
  <2>7. SI!BeginOp(h, t1) \in Range(h) /\ SI!BeginOp(h, t1).type = "begin" /\ SI!BeginOp(h, t1).txnId = t1
        /\ SI!CommitOp(h, t1) \in Range(h) /\ SI!CommitOp(h, t1).type = "commit" /\ SI!CommitOp(h, t1).txnId = t1
        /\ SI!BeginOp(h, t2) \in Range(h) /\ SI!BeginOp(h, t2).type = "begin" /\ SI!BeginOp(h, t2).txnId = t2
        /\ SI!CommitOp(h, t2) \in Range(h) /\ SI!CommitOp(h, t2).type = "commit" /\ SI!CommitOp(h, t2).txnId = t2
    BY <2>6, ChooseBegin, ChooseCommit
  <2>8. SI!CommitOp(h, t1).time < SI!BeginOp(h, t2).time
        \/ SI!CommitOp(h, t2).time < SI!BeginOp(h, t1).time
    BY <2>5, <2>7 DEF HistFacts, H3
  <2>9. ~(SI!CommitOp(h, t2).time < SI!BeginOp(h, t1).time)
    BY <1>2, <1>6, <1>7
  <2>10. SI!CommitOp(h, t1).time < SI!BeginOp(h, t2).time
    BY <2>8, <2>9
  <2>11. SI!BeginOp(h, t2).time \in Nat
    BY BeginTimeType
  <2>12. SI!CommitOp(h, t1).time \in Nat
    BY CommitTimeType
  <2>13. \E b \in Range(h) : b.type = "begin" /\ b.txnId = t2
         /\ \E c \in Range(h) : c.type = "commit" /\ c.txnId = t2
    BY DEF HistFacts, CommittedOK
  <2>14. SI!BeginOp(h, t2).time < SI!CommitOp(h, t2).time
    BY <2>13, ChooseBegin, ChooseCommit DEF HistFacts, H1
  <2>. QED
    BY <2>1, <2>2, <1>4, <1>5, <2>10, <2>11, <2>12, <2>14, <1>7
<1>. QED
  BY <1>8, <1>9

LEMMA GraphEdgeShape ==
  ASSUME NEW h, NEW e \in SI!SerializationGraph(h)
  PROVE  /\ e[1] \in SI!CommittedTxns(h)
         /\ e[2] \in SI!CommittedTxns(h)
         /\ e[1] # e[2]
         /\ \/ SI!WWDependency(h, e[1], e[2])
            \/ SI!WRDependency(h, e[1], e[2])
            \/ SI!RWDependency(h, e[1], e[2])
BY DEF SI!SerializationGraph

LEMMA EdgesIncreaseRank ==
  ASSUME NEW h, HistFacts(h),
         NEW e \in SI!SerializationGraph(h)
  PROVE  Rank(h, e[1]) \in Nat /\ Rank(h, e[2]) \in Nat /\ Rank(h, e[1]) < Rank(h, e[2])
<1>1. e[1] \in SI!CommittedTxns(h) /\ e[2] \in SI!CommittedTxns(h) /\ e[1] # e[2]
      /\ \/ SI!WWDependency(h, e[1], e[2])
         \/ SI!WRDependency(h, e[1], e[2])
         \/ SI!RWDependency(h, e[1], e[2])
  BY GraphEdgeShape
<1>2. CASE SI!WWDependency(h, e[1], e[2])
  BY <1>1, <1>2, WWEdgesRank
<1>3. CASE SI!WRDependency(h, e[1], e[2])
  BY <1>1, <1>3, WREdgesRank
<1>4. CASE SI!RWDependency(h, e[1], e[2])
  BY <1>1, <1>4, RWEdgesRank
<1>. QED
  BY <1>1, <1>2, <1>3, <1>4

LEMMA GraphNodesCommitted ==
  ASSUME NEW h, NEW t \in SI!GraphNodes(SI!SerializationGraph(h))
  PROVE  t \in SI!CommittedTxns(h)
<1>1. PICK e \in SI!SerializationGraph(h) : t = e[1] \/ t = e[2]
  BY DEF SI!GraphNodes
<1>. QED
  BY <1>1, GraphEdgeShape

LEMMA TxnIdsFinite == IsFiniteSet(TxnIds)
<1>1. TxnIds = 1..NumTxns
  BY DEF TxnIds
<1>2. NumTxns \in Nat
  BY NumTxnsNat
<1>. QED
  BY <1>1, <1>2, FS_Interval

LEMMA HistFactsSerializable ==
  ASSUME NEW h, HistFacts(h)
  PROVE  SI!IsConflictSerializableViaPath(h)
<1> DEFINE edges == SI!SerializationGraph(h)
           r(t) == Rank(h, t)
<1>1. \A e \in edges : r(e[1]) \in Nat /\ r(e[2]) \in Nat /\ r(e[1]) < r(e[2])
  BY EdgesIncreaseRank
<1>2. ~SI!IsCycleViaPath(edges)
  BY <1>1, RankedNoCycle
<1>. QED
  BY <1>2 DEF SI!IsConflictSerializableViaPath

-----------------------------------------------------------------------------
(*****************************************************************************)
(* 4.  Workload lemma: NewOrder / Payment / StockLevel satisfy H2            *)
(*****************************************************************************)

BodyH2(B) ==
  B.writes # {} =>
    \A k \in B.reads :
      \/ \E w \in B.writes : w.key = k
      \/ ReadOnlyCol(k)

NoWriteRO(h) ==
  \A op \in Range(h) :
    op.type = "body" =>
      \A w \in op.writes : ~ReadOnlyCol(w.key)

LEMMA ColumnTrue == ColumnGranularity
BY ColumnMode

LEMMA RdKeysDef ==
  ASSUME NEW base, NEW cols
  PROVE  RdKeys(base, cols) = {Item(base, c) : c \in cols}
BY ColumnTrue DEF RdKeys

LEMMA WrOpsDef ==
  ASSUME NEW snap, NEW base, NEW upd
  PROVE  WrOps(snap, base, upd) =
           {[type |-> "write", key |-> Item(base, c), val |-> upd[c]] : c \in DOMAIN upd}
BY ColumnTrue DEF WrOps

LEMMA ItemCol ==
  ASSUME NEW base, NEW col
  PROVE  Item(base, col).col = col
<1>1. Item(base, col) = [x \in (DOMAIN base) \cup {"col"} |->
                           IF x = "col" THEN col ELSE base[x]]
  BY ColumnTrue DEF Item
<1>2. "col" \in (DOMAIN base) \cup {"col"}
  OBVIOUS
<1>. QED
  BY <1>1, <1>2

LEMMA ItemTbl ==
  ASSUME NEW base, NEW col, "tbl" \in DOMAIN base
  PROVE  Item(base, col).tbl = base.tbl
<1>1. Item(base, col) = [x \in (DOMAIN base) \cup {"col"} |->
                           IF x = "col" THEN col ELSE base[x]]
  BY ColumnTrue DEF Item
<1>2. "tbl" \in (DOMAIN base) \cup {"col"}
  OBVIOUS
<1>3. "tbl" # "col"
  OBVIOUS
<1>. QED
  BY <1>1, <1>2, <1>3

LEMMA WhKeyShape ==
  ASSUME NEW w
  PROVE  WhKey(w).tbl = "WH" /\ "tbl" \in DOMAIN WhKey(w)
BY DEF WhKey

LEMMA DistKeyShape ==
  ASSUME NEW w, NEW d
  PROVE  DistKey(w, d).tbl = "DIST" /\ "tbl" \in DOMAIN DistKey(w, d)
BY DEF DistKey

LEMMA CustKeyShape ==
  ASSUME NEW w, NEW d, NEW c
  PROVE  CustKey(w, d, c).tbl = "CUST" /\ "tbl" \in DOMAIN CustKey(w, d, c)
BY DEF CustKey

LEMMA ItemKeyShape ==
  ASSUME NEW i
  PROVE  ItemKey(i).tbl = "ITEM" /\ "tbl" \in DOMAIN ItemKey(i)
BY DEF ItemKey

LEMMA StockKeyShape ==
  ASSUME NEW w, NEW i
  PROVE  StockKey(w, i).tbl = "STOCK" /\ "tbl" \in DOMAIN StockKey(w, i)
BY DEF StockKey

LEMMA OrderKeyShape ==
  ASSUME NEW w, NEW d, NEW o
  PROVE  OrderKey(w, d, o).tbl = "ORDER" /\ "tbl" \in DOMAIN OrderKey(w, d, o)
BY DEF OrderKey

LEMMA NewOrdKeyShape ==
  ASSUME NEW w, NEW d, NEW o
  PROVE  NewOrdKey(w, d, o).tbl = "NEWORDER" /\ "tbl" \in DOMAIN NewOrdKey(w, d, o)
BY DEF NewOrdKey

LEMMA OrdLineKeyShape ==
  ASSUME NEW w, NEW d, NEW o
  PROVE  OrdLineKey(w, d, o).tbl = "ORDERLINE" /\ "tbl" \in DOMAIN OrdLineKey(w, d, o)
BY DEF OrdLineKey

LEMMA HistKeyShape ==
  ASSUME NEW t
  PROVE  HistKey(t).tbl = "HIST" /\ "tbl" \in DOMAIN HistKey(t)
BY DEF HistKey

LEMMA WhTaxRO ==
  ASSUME NEW w
  PROVE  ReadOnlyCol(Item(WhKey(w), "tax"))
<1>1. Item(WhKey(w), "tax").tbl = "WH"
  BY WhKeyShape, ItemTbl
<1>2. Item(WhKey(w), "tax").col = "tax"
  BY ItemCol
<1>3. "tbl" \in DOMAIN Item(WhKey(w), "tax")
  BY ColumnTrue, WhKeyShape DEF Item
<1>4. "col" \in DOMAIN Item(WhKey(w), "tax")
  BY ColumnTrue DEF Item
<1>. QED
  BY <1>1, <1>2, <1>3, <1>4 DEF ReadOnlyCol

LEMMA DistTaxRO ==
  ASSUME NEW w, NEW d
  PROVE  ReadOnlyCol(Item(DistKey(w, d), "tax"))
<1>1. Item(DistKey(w, d), "tax").tbl = "DIST"
  BY DistKeyShape, ItemTbl
<1>2. Item(DistKey(w, d), "tax").col = "tax"
  BY ItemCol
<1>3. "tbl" \in DOMAIN Item(DistKey(w, d), "tax")
  BY ColumnTrue, DistKeyShape DEF Item
<1>4. "col" \in DOMAIN Item(DistKey(w, d), "tax")
  BY ColumnTrue DEF Item
<1>. QED
  BY <1>1, <1>2, <1>3, <1>4 DEF ReadOnlyCol

LEMMA CustInfoRO ==
  ASSUME NEW w, NEW d, NEW c
  PROVE  ReadOnlyCol(Item(CustKey(w, d, c), "info"))
<1>1. Item(CustKey(w, d, c), "info").tbl = "CUST"
  BY CustKeyShape, ItemTbl
<1>2. Item(CustKey(w, d, c), "info").col = "info"
  BY ItemCol
<1>3. "tbl" \in DOMAIN Item(CustKey(w, d, c), "info")
  BY ColumnTrue, CustKeyShape DEF Item
<1>4. "col" \in DOMAIN Item(CustKey(w, d, c), "info")
  BY ColumnTrue DEF Item
<1>. QED
  BY <1>1, <1>2, <1>3, <1>4 DEF ReadOnlyCol

LEMMA ItemInfoRO ==
  ASSUME NEW i
  PROVE  ReadOnlyCol(Item(ItemKey(i), "info"))
<1>1. Item(ItemKey(i), "info").tbl = "ITEM"
  BY ItemKeyShape, ItemTbl
<1>2. Item(ItemKey(i), "info").col = "info"
  BY ItemCol
<1>3. "tbl" \in DOMAIN Item(ItemKey(i), "info")
  BY ColumnTrue, ItemKeyShape DEF Item
<1>4. "col" \in DOMAIN Item(ItemKey(i), "info")
  BY ColumnTrue DEF Item
<1>. QED
  BY <1>1, <1>2, <1>3, <1>4 DEF ReadOnlyCol

LEMMA ItemNotRO ==
  ASSUME NEW base, NEW col,
         "tbl" \in DOMAIN base,
         ~(/\ base.tbl = "WH"   /\ col = "tax")
         /\ ~(/\ base.tbl = "DIST" /\ col = "tax")
         /\ ~(/\ base.tbl = "CUST" /\ col = "info")
         /\ ~(/\ base.tbl = "ITEM" /\ col = "info")
  PROVE  ~ReadOnlyCol(Item(base, col))
<1>1. Item(base, col).tbl = base.tbl
  BY ItemTbl
<1>2. Item(base, col).col = col
  BY ItemCol
<1>. QED
  BY <1>1, <1>2 DEF ReadOnlyCol

LEMMA WrOpsWritesItem ==
  ASSUME NEW snap, NEW base, NEW upd, NEW c \in DOMAIN upd
  PROVE  \E w \in WrOps(snap, base, upd) : w.key = Item(base, c)
<1>1. [type |-> "write", key |-> Item(base, c), val |-> upd[c]] \in WrOps(snap, base, upd)
  BY WrOpsDef
<1>. QED
  BY <1>1

LEMMA MixNoOS == "OrderStatus" \notin EnabledTxnTypes
BY RobustMix

LEMMA MixNoDelivery == "Delivery" \notin EnabledTxnTypes
BY RobustMix

LEMMA RequestType ==
  ASSUME NEW req \in Requests
  PROVE  req.type \in {"NewOrder", "Payment", "StockLevel"}
<1>1. EnabledTxnTypes \subseteq {"NewOrder", "Payment", "StockLevel"}
  BY RobustMix
<1>2. "OrderStatus" \notin EnabledTxnTypes
  BY MixNoOS
<1>3. "Delivery" \notin EnabledTxnTypes
  BY MixNoDelivery
<1>. QED
  BY <1>1, <1>2, <1>3 DEF Requests

LEMMA ProgramForNewOrder ==
  ASSUME NEW tid, NEW req, NEW snap, req.type = "NewOrder"
  PROVE  ProgramFor(tid, req, snap) = NewOrderProgram(req, snap)
BY DEF ProgramFor

LEMMA ProgramForPayment ==
  ASSUME NEW tid, NEW req, NEW snap, req.type = "Payment"
  PROVE  ProgramFor(tid, req, snap) = PaymentProgram(tid, req, snap)
BY DEF ProgramFor

LEMMA ProgramForStockLevel ==
  ASSUME NEW tid, NEW req, NEW snap, req.type = "StockLevel"
  PROVE  ProgramFor(tid, req, snap) = StockLevelProgram(req, snap)
BY DEF ProgramFor

LEMMA PaymentH2 ==
  ASSUME NEW tid, NEW req, NEW snap
  PROVE  BodyH2(PaymentProgram(tid, req, snap))
<1> DEFINE B == PaymentProgram(tid, req, snap)
           w == req.w
           d == req.d
           cw == req.cw
           cd == req.cd
           c == req.c
<1>1. B.reads = RdKeys(WhKey(w), {"ytd"})
                \cup RdKeys(DistKey(w, d), {"ytd"})
                \cup RdKeys(CustKey(cw, cd, c), {"balance"})
  BY DEF PaymentProgram
<1>2. B.writes = WrOps(snap, WhKey(w), [ytd |-> Tag])
                 \cup WrOps(snap, DistKey(w, d), [ytd |-> Tag])
                 \cup WrOps(snap, CustKey(cw, cd, c), [balance |-> Tag])
                 \cup WrOps(snap, HistKey(tid), [row |-> Tag])
  BY DEF PaymentProgram
<1> SUFFICES ASSUME B.writes # {}, NEW k \in B.reads
             PROVE  \E wr \in B.writes : wr.key = k
  BY DEF BodyH2
<1>3. k = Item(WhKey(w), "ytd")
      \/ k = Item(DistKey(w, d), "ytd")
      \/ k = Item(CustKey(cw, cd, c), "balance")
  BY <1>1, RdKeysDef
<1>4. "ytd" \in DOMAIN [ytd |-> Tag]
  OBVIOUS
<1>5. "balance" \in DOMAIN [balance |-> Tag]
  OBVIOUS
<1>6. CASE k = Item(WhKey(w), "ytd")
  <2>1. \E wr \in WrOps(snap, WhKey(w), [ytd |-> Tag]) : wr.key = Item(WhKey(w), "ytd")
    BY <1>4, WrOpsWritesItem
  <2>. QED
    BY <1>2, <1>6, <2>1
<1>7. CASE k = Item(DistKey(w, d), "ytd")
  <2>1. \E wr \in WrOps(snap, DistKey(w, d), [ytd |-> Tag]) : wr.key = Item(DistKey(w, d), "ytd")
    BY <1>4, WrOpsWritesItem
  <2>. QED
    BY <1>2, <1>7, <2>1
<1>8. CASE k = Item(CustKey(cw, cd, c), "balance")
  <2>1. \E wr \in WrOps(snap, CustKey(cw, cd, c), [balance |-> Tag]) :
           wr.key = Item(CustKey(cw, cd, c), "balance")
    BY <1>5, WrOpsWritesItem
  <2>. QED
    BY <1>2, <1>8, <2>1
<1>. QED
  BY <1>3, <1>6, <1>7, <1>8

LEMMA StockLevelH2 ==
  ASSUME NEW req, NEW snap
  PROVE  BodyH2(StockLevelProgram(req, snap))
<1>1. StockLevelProgram(req, snap).writes = {}
  BY DEF StockLevelProgram
<1>. QED
  BY <1>1 DEF BodyH2

LEMMA NewOrderH2 ==
  ASSUME NEW req, NEW snap
  PROVE  BodyH2(NewOrderProgram(req, snap))
<1> DEFINE B == NewOrderProgram(req, snap)
           w == req.w
           d == req.d
           c == req.c
           sw == req.sw
           items == req.items
           o == ColVal(snap, DistKey(w, d), "nextoid")
<1>1. B.reads = RdKeys(WhKey(w), {"tax"})
                \cup RdKeys(DistKey(w, d), {"tax", "nextoid"})
                \cup RdKeys(CustKey(w, d, c), {"info"})
                \cup (UNION {RdKeys(ItemKey(i), {"info"}) : i \in items})
                \cup (UNION {RdKeys(StockKey(sw, i), {"qty"}) : i \in items})
  BY DEF NewOrderProgram
<1>2. B.writes = WrOps(snap, DistKey(w, d), [nextoid |-> o + 1])
                 \cup (UNION {WrOps(snap, StockKey(sw, i), [qty |-> Tag]) : i \in items})
                 \cup WrOps(snap, OrderKey(w, d, o), [hdr |-> c, carrier |-> Tag])
                 \cup WrOps(snap, NewOrdKey(w, d, o), [row |-> Tag])
                 \cup WrOps(snap, OrdLineKey(w, d, o), [items |-> items, delivery |-> Tag])
  BY DEF NewOrderProgram
<1> SUFFICES ASSUME B.writes # {}, NEW k \in B.reads
             PROVE  \/ \E wr \in B.writes : wr.key = k
                    \/ ReadOnlyCol(k)
  BY DEF BodyH2
<1>3. \/ k \in RdKeys(WhKey(w), {"tax"})
      \/ k \in RdKeys(DistKey(w, d), {"tax", "nextoid"})
      \/ k \in RdKeys(CustKey(w, d, c), {"info"})
      \/ \E i \in items : k \in RdKeys(ItemKey(i), {"info"})
      \/ \E i \in items : k \in RdKeys(StockKey(sw, i), {"qty"})
  BY <1>1
<1>4. CASE k \in RdKeys(WhKey(w), {"tax"})
  <2>1. k = Item(WhKey(w), "tax")
    BY <1>4, RdKeysDef
  <2>. QED
    BY <2>1, WhTaxRO
<1>5. CASE k \in RdKeys(DistKey(w, d), {"tax", "nextoid"})
  <2>1. k = Item(DistKey(w, d), "tax") \/ k = Item(DistKey(w, d), "nextoid")
    BY <1>5, RdKeysDef
  <2>2. CASE k = Item(DistKey(w, d), "tax")
    BY <2>2, DistTaxRO
  <2>3. CASE k = Item(DistKey(w, d), "nextoid")
    <3>1. "nextoid" \in DOMAIN [nextoid |-> o + 1]
      OBVIOUS
    <3>2. \E wr \in WrOps(snap, DistKey(w, d), [nextoid |-> o + 1]) :
             wr.key = Item(DistKey(w, d), "nextoid")
      BY <3>1, WrOpsWritesItem
    <3>. QED
      BY <1>2, <2>3, <3>2
  <2>. QED
    BY <2>1, <2>2, <2>3
<1>6. CASE k \in RdKeys(CustKey(w, d, c), {"info"})
  <2>1. k = Item(CustKey(w, d, c), "info")
    BY <1>6, RdKeysDef
  <2>. QED
    BY <2>1, CustInfoRO
<1>7. CASE \E i \in items : k \in RdKeys(ItemKey(i), {"info"})
  <2>1. PICK i \in items : k \in RdKeys(ItemKey(i), {"info"})
    BY <1>7
  <2>2. k = Item(ItemKey(i), "info")
    BY <2>1, RdKeysDef
  <2>. QED
    BY <2>2, ItemInfoRO
<1>8. CASE \E i \in items : k \in RdKeys(StockKey(sw, i), {"qty"})
  <2>1. PICK i \in items : k \in RdKeys(StockKey(sw, i), {"qty"})
    BY <1>8
  <2>2. k = Item(StockKey(sw, i), "qty")
    BY <2>1, RdKeysDef
  <2>3. "qty" \in DOMAIN [qty |-> Tag]
    OBVIOUS
  <2>4. \E wr \in WrOps(snap, StockKey(sw, i), [qty |-> Tag]) :
           wr.key = Item(StockKey(sw, i), "qty")
    BY <2>3, WrOpsWritesItem
  <2>. QED
    BY <1>2, <2>2, <2>4
<1>. QED
  BY <1>3, <1>4, <1>5, <1>6, <1>7, <1>8

LEMMA PaymentNoROWrite ==
  ASSUME NEW tid, NEW req, NEW snap, NEW wr \in PaymentProgram(tid, req, snap).writes
  PROVE  ~ReadOnlyCol(wr.key)
<1> DEFINE w == req.w
           d == req.d
           cw == req.cw
           cd == req.cd
           c == req.c
<1>1. wr \in WrOps(snap, WhKey(w), [ytd |-> Tag])
      \/ wr \in WrOps(snap, DistKey(w, d), [ytd |-> Tag])
      \/ wr \in WrOps(snap, CustKey(cw, cd, c), [balance |-> Tag])
      \/ wr \in WrOps(snap, HistKey(tid), [row |-> Tag])
  BY DEF PaymentProgram
<1>2. CASE wr \in WrOps(snap, WhKey(w), [ytd |-> Tag])
  <2>1. PICK col \in DOMAIN [ytd |-> Tag] :
          wr.key = Item(WhKey(w), col)
    BY <1>2, WrOpsDef
  <2>2. col = "ytd"
    BY <2>1
  <2>3. WhKey(w).tbl = "WH"
    BY WhKeyShape
  <2>. QED
    BY <2>1, <2>2, <2>3, WhKeyShape, ItemNotRO
<1>3. CASE wr \in WrOps(snap, DistKey(w, d), [ytd |-> Tag])
  <2>1. PICK col \in DOMAIN [ytd |-> Tag] :
          wr.key = Item(DistKey(w, d), col)
    BY <1>3, WrOpsDef
  <2>2. col = "ytd"
    BY <2>1
  <2>3. DistKey(w, d).tbl = "DIST"
    BY DistKeyShape
  <2>. QED
    BY <2>1, <2>2, <2>3, DistKeyShape, ItemNotRO
<1>4. CASE wr \in WrOps(snap, CustKey(cw, cd, c), [balance |-> Tag])
  <2>1. PICK col \in DOMAIN [balance |-> Tag] :
          wr.key = Item(CustKey(cw, cd, c), col)
    BY <1>4, WrOpsDef
  <2>2. col = "balance"
    BY <2>1
  <2>3. CustKey(cw, cd, c).tbl = "CUST"
    BY CustKeyShape
  <2>. QED
    BY <2>1, <2>2, <2>3, CustKeyShape, ItemNotRO
<1>5. CASE wr \in WrOps(snap, HistKey(tid), [row |-> Tag])
  <2>1. PICK col \in DOMAIN [row |-> Tag] :
          wr.key = Item(HistKey(tid), col)
    BY <1>5, WrOpsDef
  <2>2. col = "row"
    BY <2>1
  <2>3. HistKey(tid).tbl = "HIST"
    BY HistKeyShape
  <2>. QED
    BY <2>1, <2>2, <2>3, HistKeyShape, ItemNotRO
<1>. QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5

LEMMA StockLevelNoROWrite ==
  ASSUME NEW req, NEW snap, NEW wr \in StockLevelProgram(req, snap).writes
  PROVE  ~ReadOnlyCol(wr.key)
<1>1. StockLevelProgram(req, snap).writes = {}
  BY DEF StockLevelProgram
<1>. QED
  BY <1>1

LEMMA NewOrderNoROWrite ==
  ASSUME NEW req, NEW snap, NEW wr \in NewOrderProgram(req, snap).writes
  PROVE  ~ReadOnlyCol(wr.key)
<1> DEFINE B == NewOrderProgram(req, snap)
           w == req.w
           d == req.d
           c == req.c
           sw == req.sw
           items == req.items
           o == ColVal(snap, DistKey(w, d), "nextoid")
<1>0. B.writes = WrOps(snap, DistKey(w, d), [nextoid |-> o + 1])
                 \cup (UNION {WrOps(snap, StockKey(sw, i), [qty |-> Tag]) : i \in items})
                 \cup WrOps(snap, OrderKey(w, d, o), [hdr |-> c, carrier |-> Tag])
                 \cup WrOps(snap, NewOrdKey(w, d, o), [row |-> Tag])
                 \cup WrOps(snap, OrdLineKey(w, d, o), [items |-> items, delivery |-> Tag])
  BY DEF NewOrderProgram
<1>1. wr \in WrOps(snap, DistKey(w, d), [nextoid |-> o + 1])
      \/ wr \in UNION {WrOps(snap, StockKey(sw, i), [qty |-> Tag]) : i \in items}
      \/ wr \in WrOps(snap, OrderKey(w, d, o), [hdr |-> c, carrier |-> Tag])
      \/ wr \in WrOps(snap, NewOrdKey(w, d, o), [row |-> Tag])
      \/ wr \in WrOps(snap, OrdLineKey(w, d, o), [items |-> items, delivery |-> Tag])
  BY <1>0
<1>2. CASE wr \in WrOps(snap, DistKey(w, d), [nextoid |-> o + 1])
  <2>1. PICK col \in DOMAIN [nextoid |-> o + 1] : wr.key = Item(DistKey(w, d), col)
    BY <1>2, WrOpsDef
  <2>2. col = "nextoid"
    BY <2>1
  <2>3. DistKey(w, d).tbl = "DIST"
    BY DistKeyShape
  <2>. QED
    BY <2>1, <2>2, <2>3, DistKeyShape, ItemNotRO
<1>3. CASE wr \in UNION {WrOps(snap, StockKey(sw, i), [qty |-> Tag]) : i \in items}
  <2>1. PICK i \in items : wr \in WrOps(snap, StockKey(sw, i), [qty |-> Tag])
    BY <1>3
  <2>2. PICK col \in DOMAIN [qty |-> Tag] : wr.key = Item(StockKey(sw, i), col)
    BY <2>1, WrOpsDef
  <2>3. col = "qty"
    BY <2>2
  <2>4. StockKey(sw, i).tbl = "STOCK"
    BY StockKeyShape
  <2>. QED
    BY <2>2, <2>3, <2>4, StockKeyShape, ItemNotRO
<1>4. CASE wr \in WrOps(snap, OrderKey(w, d, o), [hdr |-> c, carrier |-> Tag])
  <2>1. PICK col \in DOMAIN [hdr |-> c, carrier |-> Tag] :
          wr.key = Item(OrderKey(w, d, o), col)
    BY <1>4, WrOpsDef
  <2>2. col = "hdr" \/ col = "carrier"
    BY <2>1
  <2>3. OrderKey(w, d, o).tbl = "ORDER"
    BY OrderKeyShape
  <2>. QED
    BY <2>1, <2>2, <2>3, OrderKeyShape, ItemNotRO
<1>5. CASE wr \in WrOps(snap, NewOrdKey(w, d, o), [row |-> Tag])
  <2>1. PICK col \in DOMAIN [row |-> Tag] : wr.key = Item(NewOrdKey(w, d, o), col)
    BY <1>5, WrOpsDef
  <2>2. col = "row"
    BY <2>1
  <2>3. NewOrdKey(w, d, o).tbl = "NEWORDER"
    BY NewOrdKeyShape
  <2>. QED
    BY <2>1, <2>2, <2>3, NewOrdKeyShape, ItemNotRO
<1>6. CASE wr \in WrOps(snap, OrdLineKey(w, d, o), [items |-> items, delivery |-> Tag])
  <2>1. PICK col \in DOMAIN [items |-> items, delivery |-> Tag] :
          wr.key = Item(OrdLineKey(w, d, o), col)
    BY <1>6, WrOpsDef
  <2>2. col = "items" \/ col = "delivery"
    BY <2>1
  <2>3. OrdLineKey(w, d, o).tbl = "ORDERLINE"
    BY OrdLineKeyShape
  <2>. QED
    BY <2>1, <2>2, <2>3, OrdLineKeyShape, ItemNotRO
<1>. QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6

LEMMA WorkloadH2 ==
  ASSUME NEW tid, NEW req \in Requests, NEW snap
  PROVE  BodyH2(ProgramFor(tid, req, snap))
<1>1. req.type \in {"NewOrder", "Payment", "StockLevel"}
  BY RequestType
<1>2. CASE req.type = "NewOrder"
  <2>1. ProgramFor(tid, req, snap) = NewOrderProgram(req, snap)
    BY <1>2, ProgramForNewOrder
  <2>. QED
    BY <1>2, <2>1, NewOrderH2
<1>3. CASE req.type = "Payment"
  <2>1. ProgramFor(tid, req, snap) = PaymentProgram(tid, req, snap)
    BY <1>3, ProgramForPayment
  <2>. QED
    BY <1>3, <2>1, PaymentH2
<1>4. CASE req.type = "StockLevel"
  <2>1. ProgramFor(tid, req, snap) = StockLevelProgram(req, snap)
    BY <1>4, ProgramForStockLevel
  <2>. QED
    BY <1>4, <2>1, StockLevelH2
<1>. QED
  BY <1>1, <1>2, <1>3, <1>4

LEMMA WorkloadNoROWrite ==
  ASSUME NEW tid, NEW req \in Requests, NEW snap,
         NEW wr \in ProgramFor(tid, req, snap).writes
  PROVE  ~ReadOnlyCol(wr.key)
<1>1. req.type \in {"NewOrder", "Payment", "StockLevel"}
  BY RequestType
<1>2. CASE req.type = "NewOrder"
  <2>1. ProgramFor(tid, req, snap) = NewOrderProgram(req, snap)
    BY <1>2, ProgramForNewOrder
  <2>. QED
    BY <1>2, <2>1, NewOrderNoROWrite
<1>3. CASE req.type = "Payment"
  <2>1. ProgramFor(tid, req, snap) = PaymentProgram(tid, req, snap)
    BY <1>3, ProgramForPayment
  <2>. QED
    BY <1>3, <2>1, PaymentNoROWrite
<1>4. CASE req.type = "StockLevel"
  <2>1. ProgramFor(tid, req, snap) = StockLevelProgram(req, snap)
    BY <1>4, ProgramForStockLevel
  <2>. QED
    BY <1>4, <2>1, StockLevelNoROWrite
<1>. QED
  BY <1>1, <1>2, <1>3, <1>4

LEMMA ProgramHasRW ==
  ASSUME NEW tid, NEW req \in Requests, NEW snap
  PROVE  /\ "reads" \in DOMAIN ProgramFor(tid, req, snap)
         /\ "writes" \in DOMAIN ProgramFor(tid, req, snap)
<1>1. req.type \in {"NewOrder", "Payment", "StockLevel"}
  BY RequestType
<1>2. CASE req.type = "NewOrder"
  BY <1>2, ProgramForNewOrder DEF NewOrderProgram
<1>3. CASE req.type = "Payment"
  BY <1>3, ProgramForPayment DEF PaymentProgram
<1>4. CASE req.type = "StockLevel"
  BY <1>4, ProgramForStockLevel DEF StockLevelProgram
<1>. QED
  BY <1>1, <1>2, <1>3, <1>4

-----------------------------------------------------------------------------
(*****************************************************************************)
(* 5.  Sequence infrastructure                                               *)
(*****************************************************************************)

LEMMA PairSeq ==
  ASSUME NEW a, NEW b
  PROVE  <<a, b>> \in Seq({a, b})
<1>1. <<>> \in Seq({a, b})
  BY EmptySeq
<1>2. Append(<<>>, a) \in Seq({a, b})
  BY <1>1, AppendProperties
<1>3. Append(<<>>, a) = <<a>>
  OBVIOUS
<1>4. Append(<<a>>, b) \in Seq({a, b})
  BY <1>2, <1>3, AppendProperties
<1>5. Append(<<a>>, b) = <<a, b>>
  OBVIOUS
<1>. QED
  BY <1>4, <1>5

LEMMA RangePair ==
  ASSUME NEW a, NEW b
  PROVE  Range(<<a, b>>) = {a, b}
<1>1. <<a, b>> \in Seq({a, b})
  BY PairSeq
<1>2. Range(<<a, b>>) = { <<a, b>>[i] : i \in 1..2 }
  BY <1>1, RangeEquality
<1>. QED
  BY <1>1, <1>2, LenProperties

LEMMA HistSeqAppend ==
  ASSUME NEW S, NEW h \in Seq(S), NEW x
  PROVE  Append(h, x) \in Seq(S \cup {x})
<1>1. h \in Seq(S \cup {x})
  BY SeqMonotonic
<1>. QED
  BY <1>1, AppendProperties

LEMMA HistSeqConcatPair ==
  ASSUME NEW S, NEW h \in Seq(S), NEW a, NEW b
  PROVE  h \o <<a, b>> \in Seq(S \cup {a, b})
<1>1. h \in Seq(S \cup {a, b})
  BY SeqMonotonic
<1>2. <<a, b>> \in Seq({a, b})
  BY PairSeq
<1>3. <<a, b>> \in Seq(S \cup {a, b})
  BY <1>2, SeqMonotonic
<1>. QED
  BY <1>1, <1>3, ConcatProperties

LEMMA RangeAppend ==
  ASSUME NEW S, NEW h \in Seq(S), NEW x
  PROVE  Range(Append(h, x)) = Range(h) \cup {x}
<1>1. h \in Seq(S \cup {x})
  BY SeqMonotonic
<1>2. Append(h, x) \in Seq(S \cup {x})
  BY <1>1, AppendProperties
<1>. QED
  BY <1>1, <1>2, AppendProperties

LEMMA RangeConcatPair ==
  ASSUME NEW S, NEW h \in Seq(S), NEW a, NEW b
  PROVE  Range(h \o <<a, b>>) = Range(h) \cup {a, b}
<1>1. h \in Seq(S \cup {a, b})
  BY SeqMonotonic
<1>2. <<a, b>> \in Seq(S \cup {a, b})
  BY PairSeq, SeqMonotonic
<1>3. Range(<<a, b>>) = {a, b}
  BY RangePair
<1>. QED
  BY <1>1, <1>2, <1>3, RangeConcatenation

LEMMA NewConcatIndex ==
  ASSUME NEW S, NEW h \in Seq(S), NEW a, NEW b, NEW hp,
         hp = h \o <<a, b>>,
         hp \in Seq(S \cup {a, b}),
         NEW i \in DOMAIN hp,
         i \notin DOMAIN h
  PROVE  i = Len(h) + 1 \/ i = Len(h) + 2
<1>1. <<a, b>> \in Seq(S \cup {a, b})
  BY PairSeq, SeqMonotonic
<1>2. h \in Seq(S \cup {a, b})
  BY SeqMonotonic
<1>3. DOMAIN (h \o <<a, b>>) = 1..(Len(h) + 2)
  BY <1>1, <1>2, ConcatProperties, LenProperties
<1>4. DOMAIN hp = 1..(Len(h) + 2)
  BY <1>3
<1>5. DOMAIN h = 1..Len(h)
  BY LenProperties
<1>6. Len(h) \in Nat
  BY LenProperties
<1>7. i \in 1..(Len(h) + 2)
  BY <1>4
<1>8. i \notin 1..Len(h)
  BY <1>5
<1>. QED
  BY <1>6, <1>7, <1>8

LEMMA WritesUnchangedNonBody ==
  ASSUME NEW S, NEW h \in Seq(S), NEW x, x.type # "body"
  PROVE  \A t, k : SI!WritesKey(Append(h, x), t, k) <=> SI!WritesKey(h, t, k)
<1>1. Range(Append(h, x)) = Range(h) \cup {x}
  BY RangeAppend
<1>2. \A op \in Range(Append(h, x)) : op.type = "body" <=> op \in Range(h) /\ op.type = "body"
  BY <1>1
<1>. QED
  BY <1>1, <1>2, RangeEq DEF SI!WritesKey

LEMMA ReadsUnchangedNonBody ==
  ASSUME NEW S, NEW h \in Seq(S), NEW x, x.type # "body"
  PROVE  \A t, k : SI!ReadsKey(Append(h, x), t, k) <=> SI!ReadsKey(h, t, k)
<1>1. Range(Append(h, x)) = Range(h) \cup {x}
  BY RangeAppend
<1>2. \A op \in Range(Append(h, x)) : op.type = "body" <=> op \in Range(h) /\ op.type = "body"
  BY <1>1
<1>. QED
  BY <1>1, <1>2, RangeEq DEF SI!ReadsKey

LEMMA KeysWrittenUnchangedNonBody ==
  ASSUME NEW S, NEW h \in Seq(S), NEW x, x.type # "body"
  PROVE  \A t : SI!KeysWrittenByTxn(Append(h, x), t) = SI!KeysWrittenByTxn(h, t)
BY WritesUnchangedNonBody DEF SI!KeysWrittenByTxn

LEMMA KeysReadUnchangedNonBody ==
  ASSUME NEW S, NEW h \in Seq(S), NEW x, x.type # "body"
  PROVE  \A t : SI!KeysReadByTxn(Append(h, x), t) = SI!KeysReadByTxn(h, t)
BY ReadsUnchangedNonBody DEF SI!KeysReadByTxn

LEMMA CommittedAppendCommit ==
  ASSUME NEW S, NEW h \in Seq(S), NEW x, x.type = "commit"
  PROVE  SI!CommittedTxns(Append(h, x)) = SI!CommittedTxns(h) \cup {x.txnId}
<1>1. Range(Append(h, x)) = Range(h) \cup {x}
  BY RangeAppend
<1>. QED
  BY <1>1, RangeEq DEF SI!CommittedTxns

LEMMA CommittedAppendNonCommit ==
  ASSUME NEW S, NEW h \in Seq(S), NEW x, x.type # "commit"
  PROVE  SI!CommittedTxns(Append(h, x)) = SI!CommittedTxns(h)
<1>1. Range(Append(h, x)) = Range(h) \cup {x}
  BY RangeAppend
<1>. QED
  BY <1>1, RangeEq DEF SI!CommittedTxns

LEMMA CommittedConcatPairNonCommit ==
  ASSUME NEW S, NEW h \in Seq(S), NEW a, NEW b,
         a.type # "commit", b.type # "commit"
  PROVE  SI!CommittedTxns(h \o <<a, b>>) = SI!CommittedTxns(h)
<1>1. Range(h \o <<a, b>>) = Range(h) \cup {a, b}
  BY RangeConcatPair
<1>. QED
  BY <1>1, RangeEq DEF SI!CommittedTxns

LEMMA WritesUnchangedConcatOther ==
  ASSUME NEW S, NEW h \in Seq(S), NEW a, NEW b,
         NEW t, a.txnId # t, b.txnId # t
  PROVE  \A k : SI!WritesKey(h \o <<a, b>>, t, k) <=> SI!WritesKey(h, t, k)
<1>1. Range(h \o <<a, b>>) = Range(h) \cup {a, b}
  BY RangeConcatPair
<1>2. \A op \in Range(h \o <<a, b>>) : op.txnId = t <=> op \in Range(h) /\ op.txnId = t
  BY <1>1
<1>. QED
  BY <1>1, <1>2, RangeEq DEF SI!WritesKey

LEMMA KeysWrittenUnchangedConcatOther ==
  ASSUME NEW S, NEW h \in Seq(S), NEW a, NEW b,
         NEW t, a.txnId # t, b.txnId # t
  PROVE  SI!KeysWrittenByTxn(h \o <<a, b>>, t) = SI!KeysWrittenByTxn(h, t)
BY WritesUnchangedConcatOther DEF SI!KeysWrittenByTxn

-----------------------------------------------------------------------------
(*****************************************************************************)
(* 6.  Inductive invariant                                                   *)
(*****************************************************************************)

HistSeq == \E S : txnHistory \in Seq(S)

ClockType == clock \in Nat

OpShape ==
  \A op \in Range(txnHistory) :
    /\ "type" \in DOMAIN op
    /\ "txnId" \in DOMAIN op
    /\ op.txnId \in TxnIds
    /\ op.type \in {"begin", "body", "commit", "abort"}
    /\ op.type \in {"begin", "commit", "abort"} =>
         "time" \in DOMAIN op /\ op.time \in Nat
    /\ op.type = "body" =>
         /\ "reads" \in DOMAIN op
         /\ "writes" \in DOMAIN op
         /\ \A w \in op.writes : "key" \in DOMAIN w
    /\ op.type = "commit" =>
         "updatedKeys" \in DOMAIN op

UniqueOps ==
  \A i, j \in DOMAIN txnHistory :
    txnHistory[i].type = txnHistory[j].type /\ txnHistory[i].txnId = txnHistory[j].txnId
      => i = j

TimesMono ==
  \A i, j \in DOMAIN txnHistory :
    /\ i < j
    /\ txnHistory[i].type \in {"begin", "commit", "abort"}
    /\ txnHistory[j].type \in {"begin", "commit", "abort"}
    => txnHistory[i].time < txnHistory[j].time

TimesVsClock ==
  \A op \in Range(txnHistory) :
    op.type \in {"begin", "commit", "abort"} => op.time <= clock

OrderOK ==
  /\ \A i, j \in DOMAIN txnHistory :
        txnHistory[i].txnId = txnHistory[j].txnId
        /\ txnHistory[i].type = "begin"
        /\ txnHistory[j].type \in {"body", "commit", "abort"}
        => i < j
  /\ \A i, j \in DOMAIN txnHistory :
        txnHistory[i].txnId = txnHistory[j].txnId
        /\ txnHistory[i].type = "body"
        /\ txnHistory[j].type \in {"commit", "abort"}
        => i < j

CommitHasPreds ==
  \A c \in Range(txnHistory) :
    c.type = "commit" =>
      /\ \E b \in Range(txnHistory) : b.type = "begin" /\ b.txnId = c.txnId
      /\ \E d \in Range(txnHistory) : d.type = "body"  /\ d.txnId = c.txnId

AbortHasPreds ==
  \A a \in Range(txnHistory) :
    a.type = "abort" =>
      /\ \E b \in Range(txnHistory) : b.type = "begin" /\ b.txnId = a.txnId
      /\ \E d \in Range(txnHistory) : d.type = "body"  /\ d.txnId = a.txnId

H1inv ==
  \A b, c \in Range(txnHistory) :
    b.type = "begin" /\ c.type = "commit" /\ b.txnId = c.txnId => b.time < c.time

H2inv ==
  \A d \in Range(txnHistory) :
    d.type = "body" => BodyH2(d)

NoWriteROinv == NoWriteRO(txnHistory)

H3inv ==
  \A c1, c2 \in Range(txnHistory) :
    /\ c1.type = "commit" /\ c2.type = "commit"
    /\ c1.txnId # c2.txnId
    /\ SI!KeysWrittenByTxn(txnHistory, c1.txnId) \cap SI!KeysWrittenByTxn(txnHistory, c2.txnId) # {}
    =>
    \A b1, b2 \in Range(txnHistory) :
      b1.type = "begin" /\ b1.txnId = c1.txnId /\
      b2.type = "begin" /\ b2.txnId = c2.txnId
      => c1.time < b2.time \/ c2.time < b1.time

CommitKeys ==
  \A c \in Range(txnHistory) :
    c.type = "commit" => c.updatedKeys = SI!KeysWrittenByTxn(txnHistory, c.txnId)

RunningOK ==
  /\ runningTxns \subseteq [id : TxnIds, startTime : Nat, commitTime : {Empty}]
  /\ \A txn \in runningTxns :
        /\ \E b \in Range(txnHistory) :
              b.type = "begin" /\ b.txnId = txn.id /\ b.time = txn.startTime
        /\ \E d \in Range(txnHistory) : d.type = "body" /\ d.txnId = txn.id
        /\ ~\E c \in Range(txnHistory) : c.type \in {"commit", "abort"} /\ c.txnId = txn.id
  /\ \A t1, t2 \in runningTxns : t1.id = t2.id => t1 = t2

Inv ==
  /\ HistSeq
  /\ ClockType
  /\ OpShape
  /\ UniqueOps
  /\ TimesMono
  /\ TimesVsClock
  /\ OrderOK
  /\ CommitHasPreds
  /\ AbortHasPreds
  /\ H1inv
  /\ H2inv
  /\ NoWriteROinv
  /\ H3inv
  /\ CommitKeys
  /\ RunningOK

-----------------------------------------------------------------------------
(*****************************************************************************)
(* 7.  Inv implies HistFacts, hence serializability                          *)
(*****************************************************************************)

LEMMA UniqueOpsRangeBegin ==
  ASSUME Inv
  PROVE  UniqueBegin(txnHistory)
<1> SUFFICES ASSUME NEW op1 \in Range(txnHistory), NEW op2 \in Range(txnHistory),
                    op1.type = "begin", op2.type = "begin", op1.txnId = op2.txnId
             PROVE  op1 = op2
  BY DEF UniqueBegin
<1>1. PICK i \in DOMAIN txnHistory : txnHistory[i] = op1
  BY DEF Range
<1>2. PICK j \in DOMAIN txnHistory : txnHistory[j] = op2
  BY DEF Range
<1>. QED
  BY <1>1, <1>2 DEF Inv, UniqueOps

LEMMA UniqueOpsRangeCommit ==
  ASSUME Inv
  PROVE  UniqueCommit(txnHistory)
<1> SUFFICES ASSUME NEW op1 \in Range(txnHistory), NEW op2 \in Range(txnHistory),
                    op1.type = "commit", op2.type = "commit", op1.txnId = op2.txnId
             PROVE  op1 = op2
  BY DEF UniqueCommit
<1>1. PICK i \in DOMAIN txnHistory : txnHistory[i] = op1
  BY DEF Range
<1>2. PICK j \in DOMAIN txnHistory : txnHistory[j] = op2
  BY DEF Range
<1>. QED
  BY <1>1, <1>2 DEF Inv, UniqueOps

LEMMA UniqueOpsRangeBody ==
  ASSUME Inv
  PROVE  UniqueBody(txnHistory)
<1> SUFFICES ASSUME NEW op1 \in Range(txnHistory), NEW op2 \in Range(txnHistory),
                    op1.type = "body", op2.type = "body", op1.txnId = op2.txnId
             PROVE  op1 = op2
  BY DEF UniqueBody
<1>1. PICK i \in DOMAIN txnHistory : txnHistory[i] = op1
  BY DEF Range
<1>2. PICK j \in DOMAIN txnHistory : txnHistory[j] = op2
  BY DEF Range
<1>. QED
  BY <1>1, <1>2 DEF Inv, UniqueOps

LEMMA InvTimedOpsOK ==
  ASSUME Inv
  PROVE  TimedOpsOK(txnHistory)
BY DEF Inv, OpShape, TimedOpsOK

LEMMA InvCommittedOK ==
  ASSUME Inv
  PROVE  CommittedOK(txnHistory)
<1> SUFFICES ASSUME NEW t \in SI!CommittedTxns(txnHistory)
             PROVE  /\ \E b \in Range(txnHistory) : b.type = "begin" /\ b.txnId = t
                    /\ \E c \in Range(txnHistory) : c.type = "commit" /\ c.txnId = t
  BY DEF CommittedOK
<1>1. PICK c \in Range(txnHistory) : c.type = "commit" /\ c.txnId = t
  BY RangeEq DEF SI!CommittedTxns
<1>. QED
  BY <1>1 DEF Inv, CommitHasPreds

LEMMA InvH1 ==
  ASSUME Inv
  PROVE  H1(txnHistory)
BY DEF Inv, H1inv, H1

LEMMA InvH2 ==
  ASSUME Inv
  PROVE  H2(txnHistory)
<1> SUFFICES ASSUME NEW t \in SI!CommittedTxns(txnHistory),
                    SI!KeysWrittenByTxn(txnHistory, t) # {},
                    NEW k \in Keys,
                    SI!ReadsKey(txnHistory, t, k),
                    \E t2 \in SI!CommittedTxns(txnHistory) : SI!WritesKey(txnHistory, t2, k)
             PROVE  SI!WritesKey(txnHistory, t, k)
  BY DEF H2
<1>1. PICK t2 \in SI!CommittedTxns(txnHistory) : SI!WritesKey(txnHistory, t2, k)
  OBVIOUS
<1>2. PICK d \in Range(txnHistory) : d.txnId = t /\ d.type = "body" /\ k \in d.reads
  BY RangeEq DEF SI!ReadsKey
<1>3. BodyH2(d)
  BY <1>2 DEF Inv, H2inv
<1>4. PICK d2 \in Range(txnHistory) : d2.txnId = t /\ d2.type = "body" /\ \E w \in d2.writes : TRUE
  BY RangeEq DEF SI!KeysWrittenByTxn, SI!WritesKey
<1>5. d2 = d
  BY <1>2, <1>4, UniqueOpsRangeBody DEF UniqueBody
<1>6. d.writes # {}
  BY <1>4, <1>5
<1>7. \/ \E w \in d.writes : w.key = k
      \/ ReadOnlyCol(k)
  BY <1>2, <1>3, <1>6 DEF BodyH2
<1>8. CASE \E w \in d.writes : w.key = k
  BY <1>2, <1>8, RangeEq DEF SI!WritesKey
<1>9. CASE ReadOnlyCol(k)
  <2>1. PICK opw \in Range(txnHistory) :
          opw.txnId = t2 /\ opw.type = "body" /\ \E w \in opw.writes : w.key = k
    BY <1>1, RangeEq DEF SI!WritesKey
  <2>2. PICK w \in opw.writes : w.key = k
    BY <2>1
  <2>3. ~ReadOnlyCol(w.key)
    BY <2>1 DEF Inv, NoWriteROinv, NoWriteRO
  <2>. QED
    BY <1>9, <2>2, <2>3
<1>. QED
  BY <1>7, <1>8, <1>9

LEMMA InvH3 ==
  ASSUME Inv
  PROVE  H3(txnHistory)
<1> SUFFICES ASSUME NEW t1 \in SI!CommittedTxns(txnHistory),
                    NEW t2 \in SI!CommittedTxns(txnHistory),
                    t1 # t2,
                    SI!KeysWrittenByTxn(txnHistory, t1) \cap SI!KeysWrittenByTxn(txnHistory, t2) # {},
                    NEW b1 \in Range(txnHistory), NEW c1 \in Range(txnHistory),
                    NEW b2 \in Range(txnHistory), NEW c2 \in Range(txnHistory),
                    b1.type = "begin",  b1.txnId = t1,
                    c1.type = "commit", c1.txnId = t1,
                    b2.type = "begin",  b2.txnId = t2,
                    c2.type = "commit", c2.txnId = t2
             PROVE  c1.time < b2.time \/ c2.time < b1.time
  BY DEF H3
<1>. QED
  BY DEF Inv, H3inv

LEMMA InvHistFacts ==
  ASSUME Inv
  PROVE  HistFacts(txnHistory)
BY UniqueOpsRangeBegin, UniqueOpsRangeCommit, UniqueOpsRangeBody,
   InvTimedOpsOK, InvCommittedOK, InvH1, InvH2, InvH3
   DEF HistFacts

LEMMA InvSerializable ==
  ASSUME Inv
  PROVE  SerializableViaPath
<1>1. HistFacts(txnHistory)
  BY InvHistFacts
<1>2. SI!IsConflictSerializableViaPath(txnHistory)
  BY <1>1, HistFactsSerializable
<1>. QED
  BY <1>2 DEF SerializableViaPath, SI!SerializableViaPath

-----------------------------------------------------------------------------
(*****************************************************************************)
(* 8.  Init                                                                  *)
(*****************************************************************************)

LEMMA InitInv == Init => Inv
<1> SUFFICES ASSUME Init
             PROVE  Inv
  OBVIOUS
<1>1. txnHistory = <<>>
  BY DEF Init
<1>2. Range(txnHistory) = {}
  BY <1>1, EmptyRange
<1>3. clock = 0
  BY DEF Init
<1>4. runningTxns = {}
  BY DEF Init
<1>5. HistSeq
  <2>1. <<>> \in Seq({})
    BY EmptySeq
  <2>. QED
    BY <1>1, <2>1 DEF HistSeq
<1>6. ClockType
  BY <1>3 DEF ClockType
<1>7. OpShape
  BY <1>2 DEF OpShape
<1>8. UniqueOps
  BY <1>1 DEF UniqueOps
<1>9. TimesMono
  BY <1>1 DEF TimesMono
<1>10. TimesVsClock
  BY <1>2 DEF TimesVsClock
<1>11. OrderOK
  BY <1>1 DEF OrderOK
<1>12. CommitHasPreds
  BY <1>2 DEF CommitHasPreds
<1>13. AbortHasPreds
  BY <1>2 DEF AbortHasPreds
<1>14. H1inv
  BY <1>2 DEF H1inv
<1>15. H2inv
  BY <1>2 DEF H2inv
<1>16. NoWriteROinv
  BY <1>2 DEF NoWriteROinv, NoWriteRO
<1>17. H3inv
  BY <1>2 DEF H3inv
<1>18. CommitKeys
  BY <1>2 DEF CommitKeys
<1>19. RunningOK
  BY <1>4 DEF RunningOK
<1>. QED
  BY <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13,
     <1>14, <1>15, <1>16, <1>17, <1>18, <1>19
  DEF Inv

-----------------------------------------------------------------------------
(*****************************************************************************)
(* 9.  Stuttering                                                            *)
(*****************************************************************************)

LEMMA UnchangedInv ==
  ASSUME Inv, UNCHANGED vars
  PROVE  Inv'
BY DEF Inv, vars, HistSeq, ClockType, OpShape, UniqueOps, TimesMono, TimesVsClock,
       OrderOK, CommitHasPreds, AbortHasPreds, H1inv, H2inv, NoWriteROinv, NoWriteRO,
       H3inv, CommitKeys, RunningOK

-----------------------------------------------------------------------------
(*****************************************************************************)
(* 10. AbortTxn                                                              *)
(*****************************************************************************)

LEMMA AbortInv ==
  ASSUME Inv, NEW tid \in TxnIds, AbortTxn(tid)
  PROVE  Inv'
<1>1. PICK abortOp :
        /\ abortOp = [type |-> "abort", txnId |-> tid, time |-> clock + 1]
        /\ txnHistory' = Append(txnHistory, abortOp)
        /\ runningTxns' = {r \in runningTxns : r.id # tid}
        /\ clock' = clock + 1
        /\ UNCHANGED <<dataStore, txnSnapshots, txnProg, txnReq>>
  BY DEF AbortTxn, SI!AbortTxn
<1>2. PICK S : txnHistory \in Seq(S)
  BY DEF Inv, HistSeq
<1>3. txnHistory' \in Seq(S \cup {abortOp})
  BY <1>1, <1>2, HistSeqAppend
<1>4. Range(txnHistory') = Range(txnHistory) \cup {abortOp}
  BY <1>1, <1>2, RangeAppend
<1>5. abortOp.type = "abort" /\ abortOp.txnId = tid /\ abortOp.time = clock + 1
  BY <1>1
<1>6. clock \in Nat
  BY DEF Inv, ClockType
<1>7. tid \in SI!RunningTxnIds
  BY DEF AbortTxn, SI!AbortTxn
<1>8. PICK rtxn \in runningTxns : rtxn.id = tid
  BY <1>7 DEF SI!RunningTxnIds
<1>9. \E b \in Range(txnHistory) : b.type = "begin" /\ b.txnId = tid
      /\ \E d \in Range(txnHistory) : d.type = "body" /\ d.txnId = tid
      /\ ~\E c \in Range(txnHistory) : c.type \in {"commit", "abort"} /\ c.txnId = tid
  BY <1>8 DEF Inv, RunningOK
<1>10. HistSeq'
  BY <1>3 DEF HistSeq
<1>11. ClockType'
  BY <1>1, <1>6 DEF ClockType
<1>12. OpShape'
  <2> SUFFICES ASSUME NEW op \in Range(txnHistory')
               PROVE  /\ "type" \in DOMAIN op
                      /\ "txnId" \in DOMAIN op
                      /\ op.txnId \in TxnIds
                      /\ op.type \in {"begin", "body", "commit", "abort"}
                      /\ op.type \in {"begin", "commit", "abort"} =>
                           "time" \in DOMAIN op /\ op.time \in Nat
                      /\ op.type = "body" =>
                           /\ "reads" \in DOMAIN op
                           /\ "writes" \in DOMAIN op
                           /\ \A w \in op.writes : "key" \in DOMAIN w
                      /\ op.type = "commit" => "updatedKeys" \in DOMAIN op
    BY DEF OpShape
  <2>1. CASE op \in Range(txnHistory)
    BY <2>1 DEF Inv, OpShape
  <2>2. CASE op = abortOp
    <3>1. "type" \in DOMAIN abortOp /\ "txnId" \in DOMAIN abortOp /\ "time" \in DOMAIN abortOp
      BY <1>1
    <3>2. abortOp.txnId \in TxnIds
      BY <1>5
    <3>3. abortOp.time \in Nat
      BY <1>5, <1>6
    <3>. QED
      BY <2>2, <1>5, <3>1, <3>2, <3>3
  <2>. QED
    BY <1>4, <2>1, <2>2
<1>13. UniqueOps'
  <2> SUFFICES ASSUME NEW i \in DOMAIN txnHistory', NEW j \in DOMAIN txnHistory',
                      txnHistory'[i].type = txnHistory'[j].type,
                      txnHistory'[i].txnId = txnHistory'[j].txnId
               PROVE  i = j
    BY DEF UniqueOps
  <2>1. DOMAIN txnHistory' = 1..(Len(txnHistory)+1)
    BY <1>1, <1>2, AppendProperties, LenProperties
  <2>2. DOMAIN txnHistory = 1..Len(txnHistory)
    BY <1>2, LenProperties
  <2>3. Len(txnHistory) \in Nat
    BY <1>2, LenProperties
  <2>4. \A ii \in DOMAIN txnHistory : txnHistory'[ii] = txnHistory[ii]
    BY <1>1, <1>2, AppendProperties
  <2>5. txnHistory'[Len(txnHistory)+1] = abortOp
    BY <1>1, <1>2, AppendProperties, LenProperties
  <2>6. CASE i \in DOMAIN txnHistory /\ j \in DOMAIN txnHistory
    BY <2>4, <2>6 DEF Inv, UniqueOps
  <2>7. CASE i = Len(txnHistory)+1
    <3>1. txnHistory'[i].type = "abort" /\ txnHistory'[i].txnId = tid
      BY <2>5, <2>7, <1>5
    <3>2. CASE j \in DOMAIN txnHistory
      <4>1. txnHistory'[j] = txnHistory[j]
        BY <2>4, <3>2
      <4>2. txnHistory[j] \in Range(txnHistory)
        BY <3>2 DEF Range
      <4>3. txnHistory[j].type = "abort" /\ txnHistory[j].txnId = tid
        BY <3>1, <4>1
      <4>. QED
        BY <1>9, <4>2, <4>3
    <3>3. CASE j = Len(txnHistory)+1
      BY <2>7, <3>3
    <3>. QED
      BY <2>1, <2>2, <3>2, <3>3
  <2>8. CASE j = Len(txnHistory)+1
    <3>1. CASE i \in DOMAIN txnHistory
      <4>1. txnHistory'[j].type = "abort" /\ txnHistory'[j].txnId = tid
        BY <2>5, <2>8, <1>5
      <4>2. txnHistory'[i] = txnHistory[i]
        BY <2>4, <3>1
      <4>3. txnHistory[i] \in Range(txnHistory)
        BY <3>1 DEF Range
      <4>4. txnHistory[i].type = "abort" /\ txnHistory[i].txnId = tid
        BY <4>1, <4>2
      <4>. QED
        BY <1>9, <4>3, <4>4
    <3>2. CASE i = Len(txnHistory)+1
      BY <2>8, <3>2
    <3>. QED
      BY <2>1, <2>2, <3>1, <3>2
  <2>. QED
    BY <2>1, <2>2, <2>6, <2>7, <2>8
<1>14. TimesMono'
  <2> SUFFICES ASSUME NEW i \in DOMAIN txnHistory', NEW j \in DOMAIN txnHistory',
                      i < j,
                      txnHistory'[i].type \in {"begin", "commit", "abort"},
                      txnHistory'[j].type \in {"begin", "commit", "abort"}
               PROVE  txnHistory'[i].time < txnHistory'[j].time
    BY DEF TimesMono
  <2>1. \A ii \in DOMAIN txnHistory : txnHistory'[ii] = txnHistory[ii]
    BY <1>1, <1>2, AppendProperties
  <2>2. CASE j \in DOMAIN txnHistory
    <3>1. i \in DOMAIN txnHistory
      BY <1>1, <1>2, <2>2, AppendProperties, LenProperties
    <3>. QED
      BY <2>1, <3>1, <2>2 DEF Inv, TimesMono
  <2>3. CASE j = Len(txnHistory)+1
    <3>1. i \in DOMAIN txnHistory
      BY <2>3, <1>2, LenProperties
    <3>2. txnHistory'[i] = txnHistory[i]
      BY <2>1, <3>1
    <3>3. txnHistory[i] \in Range(txnHistory)
      BY <3>1 DEF Range
    <3>4. txnHistory[i].time <= clock
      BY <3>2, <3>3 DEF Inv, TimesVsClock, OpShape
    <3>5. txnHistory[i].time \in Nat
      BY <3>2, <3>3 DEF Inv, OpShape
    <3>6. txnHistory'[j] = abortOp
      BY <1>1, <1>2, <2>3, AppendProperties, LenProperties
    <3>. QED
      BY <3>2, <3>4, <3>5, <3>6, <1>5, <1>6
  <2>. QED
    BY <1>1, <1>2, <2>2, <2>3, AppendProperties, LenProperties
<1>15. TimesVsClock'
  <2> SUFFICES ASSUME NEW op \in Range(txnHistory'),
                      op.type \in {"begin", "commit", "abort"}
               PROVE  op.time <= clock'
    BY DEF TimesVsClock
  <2>1. CASE op \in Range(txnHistory)
    <3>1. op.time <= clock
      BY <2>1 DEF Inv, TimesVsClock
    <3>2. op.time \in Nat
      BY <2>1 DEF Inv, OpShape
    <3>. QED
      BY <1>1, <1>6, <3>1, <3>2
  <2>2. CASE op = abortOp
    BY <1>1, <1>5, <1>6, <2>2
  <2>. QED
    BY <1>4, <2>1, <2>2
<1>16. OrderOK'
  <2>1. \A ii \in DOMAIN txnHistory : txnHistory'[ii] = txnHistory[ii]
    BY <1>1, <1>2, AppendProperties
  <2>2. txnHistory'[Len(txnHistory)+1] = abortOp
    BY <1>1, <1>2, AppendProperties, LenProperties
  <2>3. \A i, j \in DOMAIN txnHistory' :
           txnHistory'[i].txnId = txnHistory'[j].txnId
           /\ txnHistory'[i].type = "begin"
           /\ txnHistory'[j].type \in {"body", "commit", "abort"}
           => i < j
    <3> SUFFICES ASSUME NEW i \in DOMAIN txnHistory', NEW j \in DOMAIN txnHistory',
                        txnHistory'[i].txnId = txnHistory'[j].txnId,
                        txnHistory'[i].type = "begin",
                        txnHistory'[j].type \in {"body", "commit", "abort"}
                 PROVE  i < j
      OBVIOUS
    <3>1. CASE i \in DOMAIN txnHistory /\ j \in DOMAIN txnHistory
      BY <2>1, <3>1 DEF Inv, OrderOK
    <3>2. CASE j = Len(txnHistory)+1
      <4>0. i # Len(txnHistory)+1
        BY <1>5, <2>2, <3>2
      <4>1. i \in DOMAIN txnHistory
        BY <1>1, <1>2, <3>2, <4>0, AppendProperties, LenProperties
      <4>2. Len(txnHistory) \in Nat
        BY <1>2, LenProperties
      <4>. QED
        BY <4>1, <3>2, <4>2
    <3>3. CASE i = Len(txnHistory)+1
      BY <1>5, <2>2, <3>3
    <3>. QED
      BY <1>1, <1>2, <3>1, <3>2, <3>3, AppendProperties, LenProperties
  <2>4. \A i, j \in DOMAIN txnHistory' :
           txnHistory'[i].txnId = txnHistory'[j].txnId
           /\ txnHistory'[i].type = "body"
           /\ txnHistory'[j].type \in {"commit", "abort"}
           => i < j
    <3> SUFFICES ASSUME NEW i \in DOMAIN txnHistory', NEW j \in DOMAIN txnHistory',
                        txnHistory'[i].txnId = txnHistory'[j].txnId,
                        txnHistory'[i].type = "body",
                        txnHistory'[j].type \in {"commit", "abort"}
                 PROVE  i < j
      OBVIOUS
    <3>1. CASE i \in DOMAIN txnHistory /\ j \in DOMAIN txnHistory
      BY <2>1, <3>1 DEF Inv, OrderOK
    <3>2. CASE j = Len(txnHistory)+1
      <4>0. i # Len(txnHistory)+1
        BY <1>5, <2>2, <3>2
      <4>1. i \in DOMAIN txnHistory
        BY <1>1, <1>2, <3>2, <4>0, AppendProperties, LenProperties
      <4>2. Len(txnHistory) \in Nat
        BY <1>2, LenProperties
      <4>. QED
        BY <4>1, <3>2, <4>2
    <3>3. CASE i = Len(txnHistory)+1
      BY <1>5, <2>2, <3>3
    <3>. QED
      BY <1>1, <1>2, <3>1, <3>2, <3>3, AppendProperties, LenProperties
  <2>. QED
    BY <2>3, <2>4 DEF OrderOK
<1>17. CommitHasPreds'
  <2> SUFFICES ASSUME NEW c \in Range(txnHistory'), c.type = "commit"
               PROVE  /\ \E b \in Range(txnHistory') : b.type = "begin" /\ b.txnId = c.txnId
                      /\ \E d \in Range(txnHistory') : d.type = "body"  /\ d.txnId = c.txnId
    BY DEF CommitHasPreds
  <2>1. c \in Range(txnHistory)
    BY <1>4, <1>5
  <2>. QED
    BY <1>4, <2>1 DEF Inv, CommitHasPreds
<1>18. AbortHasPreds'
  <2> SUFFICES ASSUME NEW a \in Range(txnHistory'), a.type = "abort"
               PROVE  /\ \E b \in Range(txnHistory') : b.type = "begin" /\ b.txnId = a.txnId
                      /\ \E d \in Range(txnHistory') : d.type = "body"  /\ d.txnId = a.txnId
    BY DEF AbortHasPreds
  <2>1. CASE a \in Range(txnHistory)
    BY <1>4, <2>1 DEF Inv, AbortHasPreds
  <2>2. CASE a = abortOp
    BY <1>4, <1>5, <1>9, <2>2
  <2>. QED
    BY <1>4, <2>1, <2>2
<1>19. H1inv'
  <2> SUFFICES ASSUME NEW b \in Range(txnHistory'), NEW c \in Range(txnHistory'),
                      b.type = "begin", c.type = "commit", b.txnId = c.txnId
               PROVE  b.time < c.time
    BY DEF H1inv
  <2>1. b \in Range(txnHistory) /\ c \in Range(txnHistory)
    BY <1>4, <1>5
  <2>. QED
    BY <2>1 DEF Inv, H1inv
<1>20. H2inv'
  <2> SUFFICES ASSUME NEW d \in Range(txnHistory'), d.type = "body"
               PROVE  BodyH2(d)
    BY DEF H2inv
  <2>1. d \in Range(txnHistory)
    BY <1>4, <1>5
  <2>. QED
    BY <2>1 DEF Inv, H2inv
<1>21. NoWriteROinv'
  <2> SUFFICES ASSUME NEW op \in Range(txnHistory'), op.type = "body",
                      NEW w \in op.writes
               PROVE  ~ReadOnlyCol(w.key)
    BY DEF NoWriteROinv, NoWriteRO
  <2>1. op \in Range(txnHistory)
    BY <1>4, <1>5
  <2>. QED
    BY <2>1 DEF Inv, NoWriteROinv, NoWriteRO
<1>22. H3inv'
  <2> SUFFICES ASSUME NEW c1 \in Range(txnHistory'), NEW c2 \in Range(txnHistory'),
                      c1.type = "commit", c2.type = "commit",
                      c1.txnId # c2.txnId,
                      SI!KeysWrittenByTxn(txnHistory', c1.txnId)
                        \cap SI!KeysWrittenByTxn(txnHistory', c2.txnId) # {}
               PROVE  \A b1, b2 \in Range(txnHistory') :
                        b1.type = "begin" /\ b1.txnId = c1.txnId /\
                        b2.type = "begin" /\ b2.txnId = c2.txnId
                        => c1.time < b2.time \/ c2.time < b1.time
    BY DEF H3inv
  <2>1. c1 \in Range(txnHistory) /\ c2 \in Range(txnHistory)
    BY <1>4, <1>5
  <2>2. SI!KeysWrittenByTxn(txnHistory', c1.txnId) = SI!KeysWrittenByTxn(txnHistory, c1.txnId)
    BY <1>1, <1>2, <1>5, KeysWrittenUnchangedNonBody
  <2>3. SI!KeysWrittenByTxn(txnHistory', c2.txnId) = SI!KeysWrittenByTxn(txnHistory, c2.txnId)
    BY <1>1, <1>2, <1>5, KeysWrittenUnchangedNonBody
  <2>4. \A b1, b2 \in Range(txnHistory) :
           b1.type = "begin" /\ b1.txnId = c1.txnId /\
           b2.type = "begin" /\ b2.txnId = c2.txnId
           => c1.time < b2.time \/ c2.time < b1.time
    BY <2>1, <2>2, <2>3 DEF Inv, H3inv
  <2>. QED
    BY <1>4, <1>5, <2>4
<1>23. CommitKeys'
  <2> SUFFICES ASSUME NEW c \in Range(txnHistory'), c.type = "commit"
               PROVE  c.updatedKeys = SI!KeysWrittenByTxn(txnHistory', c.txnId)
    BY DEF CommitKeys
  <2>1. c \in Range(txnHistory)
    BY <1>4, <1>5
  <2>2. c.updatedKeys = SI!KeysWrittenByTxn(txnHistory, c.txnId)
    BY <2>1 DEF Inv, CommitKeys
  <2>3. SI!KeysWrittenByTxn(txnHistory', c.txnId) = SI!KeysWrittenByTxn(txnHistory, c.txnId)
    BY <1>1, <1>2, <1>5, KeysWrittenUnchangedNonBody
  <2>. QED
    BY <2>2, <2>3
<1>24. RunningOK'
  <2>1. runningTxns' \subseteq [id : TxnIds, startTime : Nat, commitTime : {Empty}]
    BY <1>1 DEF Inv, RunningOK
  <2>2. \A txn \in runningTxns' :
           /\ \E b \in Range(txnHistory') :
                 b.type = "begin" /\ b.txnId = txn.id /\ b.time = txn.startTime
           /\ \E d \in Range(txnHistory') : d.type = "body" /\ d.txnId = txn.id
           /\ ~\E c \in Range(txnHistory') : c.type \in {"commit", "abort"} /\ c.txnId = txn.id
    <3> SUFFICES ASSUME NEW txn \in runningTxns'
                 PROVE  /\ \E b \in Range(txnHistory') :
                              b.type = "begin" /\ b.txnId = txn.id /\ b.time = txn.startTime
                        /\ \E d \in Range(txnHistory') : d.type = "body" /\ d.txnId = txn.id
                        /\ ~\E c \in Range(txnHistory') : c.type \in {"commit", "abort"} /\ c.txnId = txn.id
      OBVIOUS
    <3>1. txn \in runningTxns /\ txn.id # tid
      BY <1>1
    <3>2. \E b \in Range(txnHistory) :
            b.type = "begin" /\ b.txnId = txn.id /\ b.time = txn.startTime
          /\ \E d \in Range(txnHistory) : d.type = "body" /\ d.txnId = txn.id
          /\ ~\E c \in Range(txnHistory) : c.type \in {"commit", "abort"} /\ c.txnId = txn.id
      BY <3>1 DEF Inv, RunningOK
    <3>3. ~\E c \in Range(txnHistory') : c.type \in {"commit", "abort"} /\ c.txnId = txn.id
      BY <1>4, <1>5, <3>1, <3>2
    <3>. QED
      BY <1>4, <3>2, <3>3
  <2>3. \A t1, t2 \in runningTxns' : t1.id = t2.id => t1 = t2
    BY <1>1 DEF Inv, RunningOK
  <2>. QED
    BY <2>1, <2>2, <2>3 DEF RunningOK
<1>. QED
  BY <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18,
     <1>19, <1>20, <1>21, <1>22, <1>23, <1>24
  DEF Inv

-----------------------------------------------------------------------------
(*****************************************************************************)
(* 11. CommitTxn                                                             *)
(*****************************************************************************)

LEMMA TimesInjective ==
  ASSUME Inv,
         NEW op1 \in Range(txnHistory), NEW op2 \in Range(txnHistory),
         op1.type \in {"begin", "commit", "abort"},
         op2.type \in {"begin", "commit", "abort"},
         op1.time = op2.time
  PROVE  op1 = op2
<1>1. PICK i \in DOMAIN txnHistory : txnHistory[i] = op1
  BY DEF Range
<1>2. PICK j \in DOMAIN txnHistory : txnHistory[j] = op2
  BY DEF Range
<1>3. CASE i = j
  BY <1>1, <1>2, <1>3
<1>4. CASE i < j
  <2>1. op1.time < op2.time
    BY <1>1, <1>2, <1>4 DEF Inv, TimesMono
  <2>. QED
    BY <2>1
<1>5. CASE j < i
  <2>1. op2.time < op1.time
    BY <1>1, <1>2, <1>5 DEF Inv, TimesMono
  <2>. QED
    BY <2>1
<1>6. PICK S : txnHistory \in Seq(S)
  BY DEF Inv, HistSeq
<1>7. i \in 1..Len(txnHistory) /\ j \in 1..Len(txnHistory)
  BY <1>1, <1>2, <1>6, LenProperties
<1>8. Len(txnHistory) \in Nat
  BY <1>6, LenProperties
<1>. QED
  BY <1>3, <1>4, <1>5, <1>7, <1>8

LEMMA RunningHasBeginBody ==
  ASSUME Inv, NEW txn \in runningTxns
  PROVE  /\ \E b \in Range(txnHistory) : b.type = "begin" /\ b.txnId = txn.id /\ b.time = txn.startTime
         /\ \E d \in Range(txnHistory) : d.type = "body" /\ d.txnId = txn.id
         /\ ~\E c \in Range(txnHistory) : c.type \in {"commit", "abort"} /\ c.txnId = txn.id
BY DEF Inv, RunningOK

LEMMA CommitInv ==
  ASSUME Inv, NEW tid \in TxnIds, CommitTxn(tid)
  PROVE  Inv'
<1>1. PICK commitOp :
        /\ commitOp = [type |-> "commit", txnId |-> tid, time |-> clock + 1,
                       updatedKeys |-> SI!KeysWrittenByTxn(txnHistory, tid)]
        /\ txnHistory' = Append(txnHistory, commitOp)
        /\ runningTxns' = {r \in runningTxns : r.id # tid}
        /\ clock' = clock + 1
        /\ UNCHANGED <<txnSnapshots, txnProg, txnReq>>
  BY DEF CommitTxn, SI!CommitTxn
<1>2. PICK S : txnHistory \in Seq(S)
  BY DEF Inv, HistSeq
<1>3. txnHistory' \in Seq(S \cup {commitOp})
  BY <1>1, <1>2, HistSeqAppend
<1>4. Range(txnHistory') = Range(txnHistory) \cup {commitOp}
  BY <1>1, <1>2, RangeAppend
<1>5. commitOp.type = "commit" /\ commitOp.txnId = tid /\ commitOp.time = clock + 1
      /\ commitOp.updatedKeys = SI!KeysWrittenByTxn(txnHistory, tid)
  BY <1>1
<1>6. clock \in Nat
  BY DEF Inv, ClockType
<1>7. tid \in SI!RunningTxnIds
  BY DEF CommitTxn, SI!CommitTxn
<1>8. PICK rtxn \in runningTxns : rtxn.id = tid
  BY <1>7 DEF SI!RunningTxnIds
<1>9. \E b \in Range(txnHistory) : b.type = "begin" /\ b.txnId = tid /\ b.time = rtxn.startTime
      /\ \E d \in Range(txnHistory) : d.type = "body" /\ d.txnId = tid
      /\ ~\E c \in Range(txnHistory) : c.type \in {"commit", "abort"} /\ c.txnId = tid
  BY <1>8, RunningHasBeginBody
<1>10. SI!TxnCanCommit(tid)
  BY DEF CommitTxn, SI!CommitTxn
<1>11. ~\E op \in Range(txnHistory) :
          /\ op.type = "commit"
          /\ op.time > rtxn.startTime
          /\ SI!KeysWrittenByTxn(txnHistory, tid) \cap op.updatedKeys /= {}
  <2>1. PICK txn \in runningTxns :
          /\ txn.id = tid
          /\ ~\E op \in SI!Range(txnHistory) :
                /\ op.type = "commit"
                /\ op.time > txn.startTime
                /\ SI!KeysWrittenByTxn(txnHistory, tid) \cap op.updatedKeys /= {}
    BY <1>10 DEF SI!TxnCanCommit
  <2>2. txn = rtxn
    BY <1>8, <2>1 DEF Inv, RunningOK
  <2>. QED
    BY <2>1, <2>2, RangeEq
<1>12. HistSeq'
  BY <1>3 DEF HistSeq
<1>13. ClockType'
  BY <1>1, <1>6 DEF ClockType
<1>14. OpShape'
  <2> SUFFICES ASSUME NEW op \in Range(txnHistory')
               PROVE  /\ "type" \in DOMAIN op
                      /\ "txnId" \in DOMAIN op
                      /\ op.txnId \in TxnIds
                      /\ op.type \in {"begin", "body", "commit", "abort"}
                      /\ op.type \in {"begin", "commit", "abort"} =>
                           "time" \in DOMAIN op /\ op.time \in Nat
                      /\ op.type = "body" =>
                           /\ "reads" \in DOMAIN op
                           /\ "writes" \in DOMAIN op
                           /\ \A w \in op.writes : "key" \in DOMAIN w
                      /\ op.type = "commit" => "updatedKeys" \in DOMAIN op
    BY DEF OpShape
  <2>1. CASE op \in Range(txnHistory)
    BY <2>1 DEF Inv, OpShape
  <2>2. CASE op = commitOp
    <3>1. "type" \in DOMAIN commitOp /\ "txnId" \in DOMAIN commitOp
          /\ "time" \in DOMAIN commitOp /\ "updatedKeys" \in DOMAIN commitOp
      BY <1>1
    <3>2. commitOp.txnId \in TxnIds
      BY <1>5
    <3>3. commitOp.time \in Nat
      BY <1>5, <1>6
    <3>. QED
      BY <2>2, <1>5, <3>1, <3>2, <3>3
  <2>. QED
    BY <1>4, <2>1, <2>2
<1>15. UniqueOps'
  <2> SUFFICES ASSUME NEW i \in DOMAIN txnHistory', NEW j \in DOMAIN txnHistory',
                      txnHistory'[i].type = txnHistory'[j].type,
                      txnHistory'[i].txnId = txnHistory'[j].txnId
               PROVE  i = j
    BY DEF UniqueOps
  <2>1. DOMAIN txnHistory' = 1..(Len(txnHistory)+1)
    BY <1>1, <1>2, AppendProperties, LenProperties
  <2>2. DOMAIN txnHistory = 1..Len(txnHistory)
    BY <1>2, LenProperties
  <2>3. \A ii \in DOMAIN txnHistory : txnHistory'[ii] = txnHistory[ii]
    BY <1>1, <1>2, AppendProperties
  <2>4. txnHistory'[Len(txnHistory)+1] = commitOp
    BY <1>1, <1>2, AppendProperties, LenProperties
  <2>5. CASE i \in DOMAIN txnHistory /\ j \in DOMAIN txnHistory
    BY <2>3, <2>5 DEF Inv, UniqueOps
  <2>6. CASE i = Len(txnHistory)+1
    <3>1. txnHistory'[i].type = "commit" /\ txnHistory'[i].txnId = tid
      BY <2>4, <2>6, <1>5
    <3>2. CASE j \in DOMAIN txnHistory
      <4>1. txnHistory'[j] = txnHistory[j]
        BY <2>3, <3>2
      <4>2. txnHistory[j] \in Range(txnHistory)
        BY <3>2 DEF Range
      <4>3. txnHistory[j].type = "commit" /\ txnHistory[j].txnId = tid
        BY <3>1, <4>1
      <4>. QED
        BY <1>9, <4>2, <4>3
    <3>3. CASE j = Len(txnHistory)+1
      BY <2>6, <3>3
    <3>. QED
      BY <2>1, <2>2, <3>2, <3>3
  <2>7. CASE j = Len(txnHistory)+1
    <3>1. CASE i \in DOMAIN txnHistory
      <4>1. txnHistory'[j].type = "commit" /\ txnHistory'[j].txnId = tid
        BY <2>4, <2>7, <1>5
      <4>2. txnHistory'[i] = txnHistory[i]
        BY <2>3, <3>1
      <4>3. txnHistory[i] \in Range(txnHistory)
        BY <3>1 DEF Range
      <4>4. txnHistory[i].type = "commit" /\ txnHistory[i].txnId = tid
        BY <4>1, <4>2
      <4>. QED
        BY <1>9, <4>3, <4>4
    <3>2. CASE i = Len(txnHistory)+1
      BY <2>7, <3>2
    <3>. QED
      BY <2>1, <2>2, <3>1, <3>2
  <2>. QED
    BY <2>1, <2>2, <2>5, <2>6, <2>7
<1>16. TimesMono'
  <2> SUFFICES ASSUME NEW i \in DOMAIN txnHistory', NEW j \in DOMAIN txnHistory',
                      i < j,
                      txnHistory'[i].type \in {"begin", "commit", "abort"},
                      txnHistory'[j].type \in {"begin", "commit", "abort"}
               PROVE  txnHistory'[i].time < txnHistory'[j].time
    BY DEF TimesMono
  <2>1. \A ii \in DOMAIN txnHistory : txnHistory'[ii] = txnHistory[ii]
    BY <1>1, <1>2, AppendProperties
  <2>2. CASE j \in DOMAIN txnHistory
    <3>1. i \in DOMAIN txnHistory
      BY <1>1, <1>2, <2>2, AppendProperties, LenProperties
    <3>. QED
      BY <2>1, <3>1, <2>2 DEF Inv, TimesMono
  <2>3. CASE j = Len(txnHistory)+1
    <3>1. i \in DOMAIN txnHistory
      BY <2>3, <1>2, LenProperties
    <3>2. txnHistory'[i] = txnHistory[i]
      BY <2>1, <3>1
    <3>3. txnHistory[i] \in Range(txnHistory)
      BY <3>1 DEF Range
    <3>4. txnHistory[i].time <= clock
      BY <3>2, <3>3 DEF Inv, TimesVsClock, OpShape
    <3>5. txnHistory[i].time \in Nat
      BY <3>2, <3>3 DEF Inv, OpShape
    <3>6. txnHistory'[j] = commitOp
      BY <1>1, <1>2, <2>3, AppendProperties, LenProperties
    <3>. QED
      BY <3>2, <3>4, <3>5, <3>6, <1>5, <1>6
  <2>. QED
    BY <1>1, <1>2, <2>2, <2>3, AppendProperties, LenProperties
<1>17. TimesVsClock'
  <2> SUFFICES ASSUME NEW op \in Range(txnHistory'),
                      op.type \in {"begin", "commit", "abort"}
               PROVE  op.time <= clock'
    BY DEF TimesVsClock
  <2>1. CASE op \in Range(txnHistory)
    <3>1. op.time <= clock
      BY <2>1 DEF Inv, TimesVsClock
    <3>2. op.time \in Nat
      BY <2>1 DEF Inv, OpShape
    <3>. QED
      BY <1>1, <1>6, <3>1, <3>2
  <2>2. CASE op = commitOp
    BY <1>1, <1>5, <1>6, <2>2
  <2>. QED
    BY <1>4, <2>1, <2>2
<1>18. OrderOK'
  <2>1. \A ii \in DOMAIN txnHistory : txnHistory'[ii] = txnHistory[ii]
    BY <1>1, <1>2, AppendProperties
  <2>2. txnHistory'[Len(txnHistory)+1] = commitOp
    BY <1>1, <1>2, AppendProperties, LenProperties
  <2>3. \A i, j \in DOMAIN txnHistory' :
           txnHistory'[i].txnId = txnHistory'[j].txnId
           /\ txnHistory'[i].type = "begin"
           /\ txnHistory'[j].type \in {"body", "commit", "abort"}
           => i < j
    <3> SUFFICES ASSUME NEW i \in DOMAIN txnHistory', NEW j \in DOMAIN txnHistory',
                        txnHistory'[i].txnId = txnHistory'[j].txnId,
                        txnHistory'[i].type = "begin",
                        txnHistory'[j].type \in {"body", "commit", "abort"}
                 PROVE  i < j
      OBVIOUS
    <3>1. CASE i \in DOMAIN txnHistory /\ j \in DOMAIN txnHistory
      BY <2>1, <3>1 DEF Inv, OrderOK
    <3>2. CASE j = Len(txnHistory)+1
      <4>0. i # Len(txnHistory)+1
        BY <1>5, <2>2, <3>2
      <4>1. i \in DOMAIN txnHistory
        BY <1>1, <1>2, <3>2, <4>0, AppendProperties, LenProperties
      <4>2. Len(txnHistory) \in Nat
        BY <1>2, LenProperties
      <4>. QED
        BY <4>1, <3>2, <4>2
    <3>3. CASE i = Len(txnHistory)+1
      BY <1>5, <2>2, <3>3
    <3>. QED
      BY <1>1, <1>2, <3>1, <3>2, <3>3, AppendProperties, LenProperties
  <2>4. \A i, j \in DOMAIN txnHistory' :
           txnHistory'[i].txnId = txnHistory'[j].txnId
           /\ txnHistory'[i].type = "body"
           /\ txnHistory'[j].type \in {"commit", "abort"}
           => i < j
    <3> SUFFICES ASSUME NEW i \in DOMAIN txnHistory', NEW j \in DOMAIN txnHistory',
                        txnHistory'[i].txnId = txnHistory'[j].txnId,
                        txnHistory'[i].type = "body",
                        txnHistory'[j].type \in {"commit", "abort"}
                 PROVE  i < j
      OBVIOUS
    <3>1. CASE i \in DOMAIN txnHistory /\ j \in DOMAIN txnHistory
      BY <2>1, <3>1 DEF Inv, OrderOK
    <3>2. CASE j = Len(txnHistory)+1
      <4>0. i # Len(txnHistory)+1
        BY <1>5, <2>2, <3>2
      <4>1. i \in DOMAIN txnHistory
        BY <1>1, <1>2, <3>2, <4>0, AppendProperties, LenProperties
      <4>2. Len(txnHistory) \in Nat
        BY <1>2, LenProperties
      <4>. QED
        BY <4>1, <3>2, <4>2
    <3>3. CASE i = Len(txnHistory)+1
      BY <1>5, <2>2, <3>3
    <3>. QED
      BY <1>1, <1>2, <3>1, <3>2, <3>3, AppendProperties, LenProperties
  <2>. QED
    BY <2>3, <2>4 DEF OrderOK
<1>19. CommitHasPreds'
  <2> SUFFICES ASSUME NEW c \in Range(txnHistory'), c.type = "commit"
               PROVE  /\ \E b \in Range(txnHistory') : b.type = "begin" /\ b.txnId = c.txnId
                      /\ \E d \in Range(txnHistory') : d.type = "body"  /\ d.txnId = c.txnId
    BY DEF CommitHasPreds
  <2>1. CASE c \in Range(txnHistory)
    BY <1>4, <2>1 DEF Inv, CommitHasPreds
  <2>2. CASE c = commitOp
    BY <1>4, <1>5, <1>9, <2>2
  <2>. QED
    BY <1>4, <2>1, <2>2
<1>20. AbortHasPreds'
  <2> SUFFICES ASSUME NEW a \in Range(txnHistory'), a.type = "abort"
               PROVE  /\ \E b \in Range(txnHistory') : b.type = "begin" /\ b.txnId = a.txnId
                      /\ \E d \in Range(txnHistory') : d.type = "body"  /\ d.txnId = a.txnId
    BY DEF AbortHasPreds
  <2>1. a \in Range(txnHistory)
    BY <1>4, <1>5
  <2>. QED
    BY <1>4, <2>1 DEF Inv, AbortHasPreds
<1>21. H1inv'
  <2> SUFFICES ASSUME NEW b \in Range(txnHistory'), NEW c \in Range(txnHistory'),
                      b.type = "begin", c.type = "commit", b.txnId = c.txnId
               PROVE  b.time < c.time
    BY DEF H1inv
  <2>1. CASE c \in Range(txnHistory)
    <3>1. b \in Range(txnHistory)
      BY <1>4, <1>5, <2>1
    <3>. QED
      BY <2>1, <3>1 DEF Inv, H1inv
  <2>2. CASE c = commitOp
    <3>1. b \in Range(txnHistory)
      BY <1>4, <1>5, <2>2
    <3>2. b.txnId = tid
      BY <1>5, <2>2
    <3>3. b.time <= clock
      BY <3>1 DEF Inv, TimesVsClock
    <3>4. b.time \in Nat
      BY <3>1 DEF Inv, OpShape
    <3>. QED
      BY <1>5, <1>6, <2>2, <3>3, <3>4
  <2>. QED
    BY <1>4, <2>1, <2>2
<1>22. H2inv'
  <2> SUFFICES ASSUME NEW d \in Range(txnHistory'), d.type = "body"
               PROVE  BodyH2(d)
    BY DEF H2inv
  <2>1. d \in Range(txnHistory)
    BY <1>4, <1>5
  <2>. QED
    BY <2>1 DEF Inv, H2inv
<1>23. NoWriteROinv'
  <2> SUFFICES ASSUME NEW op \in Range(txnHistory'), op.type = "body",
                      NEW w \in op.writes
               PROVE  ~ReadOnlyCol(w.key)
    BY DEF NoWriteROinv, NoWriteRO
  <2>1. op \in Range(txnHistory)
    BY <1>4, <1>5
  <2>. QED
    BY <2>1 DEF Inv, NoWriteROinv, NoWriteRO
<1>24. H3inv'
  <2> SUFFICES ASSUME NEW c1 \in Range(txnHistory'), NEW c2 \in Range(txnHistory'),
                      c1.type = "commit", c2.type = "commit",
                      c1.txnId # c2.txnId,
                      SI!KeysWrittenByTxn(txnHistory', c1.txnId)
                        \cap SI!KeysWrittenByTxn(txnHistory', c2.txnId) # {},
                      NEW b1 \in Range(txnHistory'), NEW b2 \in Range(txnHistory'),
                      b1.type = "begin", b1.txnId = c1.txnId,
                      b2.type = "begin", b2.txnId = c2.txnId
               PROVE  c1.time < b2.time \/ c2.time < b1.time
    BY DEF H3inv
  <2>1. SI!KeysWrittenByTxn(txnHistory', c1.txnId) = SI!KeysWrittenByTxn(txnHistory, c1.txnId)
    BY <1>1, <1>2, <1>5, KeysWrittenUnchangedNonBody
  <2>2. SI!KeysWrittenByTxn(txnHistory', c2.txnId) = SI!KeysWrittenByTxn(txnHistory, c2.txnId)
    BY <1>1, <1>2, <1>5, KeysWrittenUnchangedNonBody
  <2>3. CASE c1 \in Range(txnHistory) /\ c2 \in Range(txnHistory)
    <3>1. b1 \in Range(txnHistory) /\ b2 \in Range(txnHistory)
      BY <1>4, <1>5
    <3>. QED
      BY <2>1, <2>2, <2>3, <3>1 DEF Inv, H3inv
  <2>4. CASE c2 = commitOp
    <3>1. c1 \in Range(txnHistory)
      BY <1>4, <1>5, <2>4
    <3>2. b2.txnId = tid
      BY <1>5, <2>4
    <3>3. b2 \in Range(txnHistory)
      BY <1>4, <1>5
    <3>4. b2.time = rtxn.startTime
      BY <1>9, <3>2, <3>3, UniqueOpsRangeBegin DEF UniqueBegin
    <3>5. c1.updatedKeys = SI!KeysWrittenByTxn(txnHistory, c1.txnId)
      BY <3>1 DEF Inv, CommitKeys
    <3>6. SI!KeysWrittenByTxn(txnHistory, tid) \cap c1.updatedKeys # {}
      BY <2>1, <2>2, <1>5, <2>4, <3>5
    <3>7. ~(c1.time > rtxn.startTime)
      BY <1>11, <3>1, <3>6
    <3>8. c1.time \in Nat /\ rtxn.startTime \in Nat
      BY <1>8, <3>1 DEF Inv, OpShape, RunningOK
    <3>9. c1.time <= rtxn.startTime
      BY <3>7, <3>8
    <3>10. c1.time # rtxn.startTime
      <4>1. b2.type \in {"begin", "commit", "abort"} /\ c1.type \in {"begin", "commit", "abort"}
        OBVIOUS
      <4>2. c1.time = b2.time => c1 = b2
        BY <3>1, <3>3, <4>1, TimesInjective
      <4>. QED
        BY <3>1, <3>4, <4>2
    <3>. QED
      BY <3>4, <3>8, <3>9, <3>10
  <2>5. CASE c1 = commitOp
    <3>1. c2 \in Range(txnHistory)
      BY <1>4, <1>5, <2>5
    <3>2. b1.txnId = tid
      BY <1>5, <2>5
    <3>3. b1 \in Range(txnHistory)
      BY <1>4, <1>5
    <3>4. b1.time = rtxn.startTime
      BY <1>9, <3>2, <3>3, UniqueOpsRangeBegin DEF UniqueBegin
    <3>5. c2.updatedKeys = SI!KeysWrittenByTxn(txnHistory, c2.txnId)
      BY <3>1 DEF Inv, CommitKeys
    <3>6. SI!KeysWrittenByTxn(txnHistory, tid) \cap c2.updatedKeys # {}
      BY <2>1, <2>2, <1>5, <2>5, <3>5
    <3>7. ~(c2.time > rtxn.startTime)
      BY <1>11, <3>1, <3>6
    <3>8. c2.time \in Nat /\ rtxn.startTime \in Nat
      BY <1>8, <3>1 DEF Inv, OpShape, RunningOK
    <3>9. c2.time <= rtxn.startTime
      BY <3>7, <3>8
    <3>10. c2.time # rtxn.startTime
      <4>1. b1.type \in {"begin", "commit", "abort"} /\ c2.type \in {"begin", "commit", "abort"}
        OBVIOUS
      <4>2. c2.time = b1.time => c2 = b1
        BY <3>1, <3>3, <4>1, TimesInjective
      <4>. QED
        BY <3>1, <3>4, <4>2
    <3>. QED
      BY <3>4, <3>8, <3>9, <3>10
  <2>. QED
    BY <1>4, <2>3, <2>4, <2>5
<1>25. CommitKeys'
  <2> SUFFICES ASSUME NEW c \in Range(txnHistory'), c.type = "commit"
               PROVE  c.updatedKeys = SI!KeysWrittenByTxn(txnHistory', c.txnId)
    BY DEF CommitKeys
  <2>1. SI!KeysWrittenByTxn(txnHistory', c.txnId) = SI!KeysWrittenByTxn(txnHistory, c.txnId)
    BY <1>1, <1>2, <1>5, KeysWrittenUnchangedNonBody
  <2>2. CASE c \in Range(txnHistory)
    BY <2>1, <2>2 DEF Inv, CommitKeys
  <2>3. CASE c = commitOp
    BY <1>5, <2>1, <2>3
  <2>. QED
    BY <1>4, <2>2, <2>3
<1>26. RunningOK'
  <2>1. runningTxns' \subseteq [id : TxnIds, startTime : Nat, commitTime : {Empty}]
    BY <1>1 DEF Inv, RunningOK
  <2>2. \A txn \in runningTxns' :
           /\ \E b \in Range(txnHistory') :
                 b.type = "begin" /\ b.txnId = txn.id /\ b.time = txn.startTime
           /\ \E d \in Range(txnHistory') : d.type = "body" /\ d.txnId = txn.id
           /\ ~\E c \in Range(txnHistory') : c.type \in {"commit", "abort"} /\ c.txnId = txn.id
    <3> SUFFICES ASSUME NEW txn \in runningTxns'
                 PROVE  /\ \E b \in Range(txnHistory') :
                              b.type = "begin" /\ b.txnId = txn.id /\ b.time = txn.startTime
                        /\ \E d \in Range(txnHistory') : d.type = "body" /\ d.txnId = txn.id
                        /\ ~\E c \in Range(txnHistory') : c.type \in {"commit", "abort"} /\ c.txnId = txn.id
      OBVIOUS
    <3>1. txn \in runningTxns /\ txn.id # tid
      BY <1>1
    <3>2. \E b \in Range(txnHistory) :
            b.type = "begin" /\ b.txnId = txn.id /\ b.time = txn.startTime
          /\ \E d \in Range(txnHistory) : d.type = "body" /\ d.txnId = txn.id
          /\ ~\E c \in Range(txnHistory) : c.type \in {"commit", "abort"} /\ c.txnId = txn.id
      BY <3>1, RunningHasBeginBody
    <3>3. ~\E c \in Range(txnHistory') : c.type \in {"commit", "abort"} /\ c.txnId = txn.id
      BY <1>4, <1>5, <3>1, <3>2
    <3>. QED
      BY <1>4, <3>2, <3>3
  <2>3. \A t1, t2 \in runningTxns' : t1.id = t2.id => t1 = t2
    BY <1>1 DEF Inv, RunningOK
  <2>. QED
    BY <2>1, <2>2, <2>3 DEF RunningOK
<1>. QED
  BY <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, <1>19, <1>20,
     <1>21, <1>22, <1>23, <1>24, <1>25, <1>26
  DEF Inv

-----------------------------------------------------------------------------
(*****************************************************************************)
(* 12. StartAndRun                                                           *)
(*****************************************************************************)

LEMMA ProgramWritesHaveKey ==
  ASSUME NEW tid, NEW req \in Requests, NEW snap,
         NEW w \in ProgramFor(tid, req, snap).writes
  PROVE  "key" \in DOMAIN w
<1>1. req.type \in {"NewOrder", "Payment", "StockLevel"}
  BY RequestType
<1>2. CASE req.type = "Payment"
  <2>1. ProgramFor(tid, req, snap) = PaymentProgram(tid, req, snap)
    BY <1>2, ProgramForPayment
  <2>2. w \in WrOps(snap, WhKey(req.w), [ytd |-> Tag])
        \/ w \in WrOps(snap, DistKey(req.w, req.d), [ytd |-> Tag])
        \/ w \in WrOps(snap, CustKey(req.cw, req.cd, req.c), [balance |-> Tag])
        \/ w \in WrOps(snap, HistKey(tid), [row |-> Tag])
    BY <2>1 DEF PaymentProgram
  <2>. QED
    BY <2>2, WrOpsDef
<1>3. CASE req.type = "StockLevel"
  <2>1. ProgramFor(tid, req, snap) = StockLevelProgram(req, snap)
    BY <1>3, ProgramForStockLevel
  <2>2. StockLevelProgram(req, snap).writes = {}
    BY DEF StockLevelProgram
  <2>. QED
    BY <2>1, <2>2
<1>4. CASE req.type = "NewOrder"
  <2> DEFINE B == NewOrderProgram(req, snap)
             w0 == req.w
             d == req.d
             c == req.c
             sw == req.sw
             items == req.items
             o == ColVal(snap, DistKey(w0, d), "nextoid")
  <2>1. ProgramFor(tid, req, snap) = B
    BY <1>4, ProgramForNewOrder
  <2>2. B.writes = WrOps(snap, DistKey(w0, d), [nextoid |-> o + 1])
                   \cup (UNION {WrOps(snap, StockKey(sw, i), [qty |-> Tag]) : i \in items})
                   \cup WrOps(snap, OrderKey(w0, d, o), [hdr |-> c, carrier |-> Tag])
                   \cup WrOps(snap, NewOrdKey(w0, d, o), [row |-> Tag])
                   \cup WrOps(snap, OrdLineKey(w0, d, o), [items |-> items, delivery |-> Tag])
    BY DEF NewOrderProgram
  <2>3. w \in WrOps(snap, DistKey(w0, d), [nextoid |-> o + 1])
        \/ w \in UNION {WrOps(snap, StockKey(sw, i), [qty |-> Tag]) : i \in items}
        \/ w \in WrOps(snap, OrderKey(w0, d, o), [hdr |-> c, carrier |-> Tag])
        \/ w \in WrOps(snap, NewOrdKey(w0, d, o), [row |-> Tag])
        \/ w \in WrOps(snap, OrdLineKey(w0, d, o), [items |-> items, delivery |-> Tag])
    BY <2>1, <2>2
  <2>. QED
    BY <2>3, WrOpsDef
<1>. QED
  BY <1>1, <1>2, <1>3, <1>4

LEMMA StartInv ==
  ASSUME Inv, NEW tid \in TxnIds, NEW req \in Requests, StartAndRun(tid, req)
  PROVE  Inv'
<1> DEFINE body == ProgramFor(tid, req, dataStore)
           beginOp == [type |-> "begin", txnId |-> tid, time |-> clock + 1]
           bodyOp == [type |-> "body", txnId |-> tid, reads |-> body.reads, writes |-> body.writes]
           newTxn == [id |-> tid, startTime |-> clock + 1, commitTime |-> Empty]
<1>1. /\ ~\E op \in SI!Range(txnHistory) : op.txnId = tid
      /\ txnHistory' = txnHistory \o <<beginOp, bodyOp>>
      /\ runningTxns' = runningTxns \cup {newTxn}
      /\ clock' = clock + 1
      /\ UNCHANGED dataStore
  BY DEF StartAndRun, SI!StartAndRun
<1>2. PICK S : txnHistory \in Seq(S)
  BY DEF Inv, HistSeq
<1>3. txnHistory' \in Seq(S \cup {beginOp, bodyOp})
  BY <1>1, <1>2, HistSeqConcatPair
<1>4. Range(txnHistory') = Range(txnHistory) \cup {beginOp, bodyOp}
  BY <1>1, <1>2, RangeConcatPair
<1>5. beginOp.type = "begin" /\ beginOp.txnId = tid /\ beginOp.time = clock + 1
      /\ bodyOp.type = "body" /\ bodyOp.txnId = tid
      /\ bodyOp.reads = body.reads /\ bodyOp.writes = body.writes
  OBVIOUS
<1>6. clock \in Nat
  BY DEF Inv, ClockType
<1>7. ~\E op \in Range(txnHistory) : op.txnId = tid
  BY <1>1, RangeEq
<1>8. BodyH2(body)
  BY WorkloadH2
<1>9. "reads" \in DOMAIN body /\ "writes" \in DOMAIN body
  BY ProgramHasRW
<1>10. HistSeq'
  BY <1>3 DEF HistSeq
<1>11. ClockType'
  BY <1>1, <1>6 DEF ClockType
<1>12. OpShape'
  <2> SUFFICES ASSUME NEW op \in Range(txnHistory')
               PROVE  /\ "type" \in DOMAIN op
                      /\ "txnId" \in DOMAIN op
                      /\ op.txnId \in TxnIds
                      /\ op.type \in {"begin", "body", "commit", "abort"}
                      /\ op.type \in {"begin", "commit", "abort"} =>
                           "time" \in DOMAIN op /\ op.time \in Nat
                      /\ op.type = "body" =>
                           /\ "reads" \in DOMAIN op
                           /\ "writes" \in DOMAIN op
                           /\ \A w \in op.writes : "key" \in DOMAIN w
                      /\ op.type = "commit" => "updatedKeys" \in DOMAIN op
    BY DEF OpShape
  <2>1. CASE op \in Range(txnHistory)
    BY <2>1 DEF Inv, OpShape
  <2>2. CASE op = beginOp
    <3>1. "type" \in DOMAIN beginOp /\ "txnId" \in DOMAIN beginOp /\ "time" \in DOMAIN beginOp
      OBVIOUS
    <3>2. beginOp.time \in Nat
      BY <1>5, <1>6
    <3>. QED
      BY <2>2, <1>5, <3>1, <3>2
  <2>3. CASE op = bodyOp
    <3>1. "type" \in DOMAIN bodyOp /\ "txnId" \in DOMAIN bodyOp
          /\ "reads" \in DOMAIN bodyOp /\ "writes" \in DOMAIN bodyOp
      BY <1>5, <1>9
    <3>2. \A w \in bodyOp.writes : "key" \in DOMAIN w
      BY <1>5, ProgramWritesHaveKey
    <3>. QED
      BY <2>3, <1>5, <3>1, <3>2
  <2>. QED
    BY <1>4, <2>1, <2>2, <2>3
<1>13. UniqueOps'
  <2> SUFFICES ASSUME NEW i \in DOMAIN txnHistory', NEW j \in DOMAIN txnHistory',
                      txnHistory'[i].type = txnHistory'[j].type,
                      txnHistory'[i].txnId = txnHistory'[j].txnId
               PROVE  i = j
    BY DEF UniqueOps
  <2>1. DOMAIN txnHistory' = 1..(Len(txnHistory)+2)
    BY <1>1, <1>2, <1>3, ConcatProperties, PairSeq, SeqMonotonic, LenProperties
  <2>2. DOMAIN txnHistory = 1..Len(txnHistory)
    BY <1>2, LenProperties
  <2>3. Len(txnHistory) \in Nat
    BY <1>2, LenProperties
  <2>4. <<beginOp, bodyOp>> \in Seq(S \cup {beginOp, bodyOp})
    BY PairSeq, SeqMonotonic
  <2>5. \A ii \in DOMAIN txnHistory : txnHistory'[ii] = txnHistory[ii]
    BY <1>1, <1>2, <2>4, ConcatProperties, LenProperties
  <2>6. txnHistory'[Len(txnHistory)+1] = beginOp
    BY <1>1, <1>2, <2>4, ConcatProperties, LenProperties
  <2>7. txnHistory'[Len(txnHistory)+2] = bodyOp
    BY <1>1, <1>2, <2>4, ConcatProperties, LenProperties
  <2>8. CASE i \in DOMAIN txnHistory /\ j \in DOMAIN txnHistory
    BY <2>5, <2>8 DEF Inv, UniqueOps
  <2>9. CASE i \in {Len(txnHistory)+1, Len(txnHistory)+2} /\ j \in DOMAIN txnHistory
    <3>1. txnHistory'[i].txnId = tid
      BY <2>9, <1>5, <2>6, <2>7
    <3>2. txnHistory'[j] = txnHistory[j]
      BY <2>5, <2>9
    <3>3. txnHistory[j] \in Range(txnHistory)
      BY <2>2, <2>9 DEF Range
    <3>4. txnHistory[j].txnId = tid
      BY <3>1, <3>2
    <3>. QED
      BY <1>7, <3>3, <3>4
  <2>10. CASE j \in {Len(txnHistory)+1, Len(txnHistory)+2} /\ i \in DOMAIN txnHistory
    <3>1. txnHistory'[j].txnId = tid
      BY <2>10, <1>5, <2>6, <2>7
    <3>2. txnHistory'[i] = txnHistory[i]
      BY <2>5, <2>10
    <3>3. txnHistory[i] \in Range(txnHistory)
      BY <2>2, <2>10 DEF Range
    <3>4. txnHistory[i].txnId = tid
      BY <3>1, <3>2
    <3>. QED
      BY <1>7, <3>3, <3>4
  <2>11. CASE i \in {Len(txnHistory)+1, Len(txnHistory)+2} /\ j \in {Len(txnHistory)+1, Len(txnHistory)+2}
    <3>1. CASE i = j
      BY <3>1
    <3>2. CASE i # j
      <4>1. CASE i = Len(txnHistory)+1
        <5>1. j = Len(txnHistory)+2
          BY <2>11, <3>2, <4>1
        <5>2. txnHistory'[i].type = "begin"
          BY <2>6, <4>1, <1>5
        <5>3. txnHistory'[j].type = "body"
          BY <2>7, <5>1, <1>5
        <5>. QED
          BY <5>2, <5>3
      <4>2. CASE i = Len(txnHistory)+2
        <5>1. j = Len(txnHistory)+1
          BY <2>11, <3>2, <4>2
        <5>2. txnHistory'[i].type = "body"
          BY <2>7, <4>2, <1>5
        <5>3. txnHistory'[j].type = "begin"
          BY <2>6, <5>1, <1>5
        <5>. QED
          BY <5>2, <5>3
      <4>. QED
        BY <2>11, <4>1, <4>2
    <3>. QED
      BY <3>1, <3>2
  <2>. QED
    BY <2>1, <2>2, <2>8, <2>9, <2>10, <2>11
<1>14. TimesMono'
  <2> SUFFICES ASSUME NEW i \in DOMAIN txnHistory', NEW j \in DOMAIN txnHistory',
                      i < j,
                      txnHistory'[i].type \in {"begin", "commit", "abort"},
                      txnHistory'[j].type \in {"begin", "commit", "abort"}
               PROVE  txnHistory'[i].time < txnHistory'[j].time
    BY DEF TimesMono
  <2>1. DOMAIN txnHistory = 1..Len(txnHistory)
    BY <1>2, LenProperties
  <2>2. <<beginOp, bodyOp>> \in Seq(S \cup {beginOp, bodyOp})
    BY PairSeq, SeqMonotonic
  <2>3. \A ii \in DOMAIN txnHistory : txnHistory'[ii] = txnHistory[ii]
    BY <1>1, <1>2, <2>2, ConcatProperties, LenProperties
  <2>4. txnHistory'[Len(txnHistory)+1] = beginOp
    BY <1>1, <1>2, <2>2, ConcatProperties, LenProperties
  <2>5. txnHistory'[Len(txnHistory)+2] = bodyOp
    BY <1>1, <1>2, <2>2, ConcatProperties, LenProperties
  <2>6. CASE j \in DOMAIN txnHistory
    <3>1. i \in DOMAIN txnHistory
      BY <1>1, <1>2, <2>6, ConcatProperties, LenProperties
    <3>. QED
      BY <2>3, <3>1, <2>6 DEF Inv, TimesMono
  <2>7. CASE j = Len(txnHistory)+1
    <3>1. i \in DOMAIN txnHistory
      BY <2>7, <1>2, LenProperties
    <3>2. txnHistory'[i] = txnHistory[i]
      BY <2>3, <3>1
    <3>3. txnHistory[i] \in Range(txnHistory)
      BY <3>1 DEF Range
    <3>4. txnHistory[i].time <= clock
      BY <3>2, <3>3 DEF Inv, TimesVsClock, OpShape
    <3>5. txnHistory[i].time \in Nat
      BY <3>2, <3>3 DEF Inv, OpShape
    <3>. QED
      BY <2>4, <2>7, <3>2, <3>4, <3>5, <1>5, <1>6
  <2>8. CASE j = Len(txnHistory)+2
    <3>1. txnHistory'[j] = bodyOp
      BY <2>5, <2>8
    <3>. QED
      BY <1>5, <3>1
  <2>. QED
    BY <1>1, <1>2, <1>3, <2>1, <2>6, <2>7, <2>8, ConcatProperties, LenProperties, PairSeq, SeqMonotonic
<1>15. TimesVsClock'
  <2> SUFFICES ASSUME NEW op \in Range(txnHistory'),
                      op.type \in {"begin", "commit", "abort"}
               PROVE  op.time <= clock'
    BY DEF TimesVsClock
  <2>1. CASE op \in Range(txnHistory)
    <3>1. op.time <= clock
      BY <2>1 DEF Inv, TimesVsClock
    <3>2. op.time \in Nat
      BY <2>1 DEF Inv, OpShape
    <3>. QED
      BY <1>1, <1>6, <3>1, <3>2
  <2>2. CASE op = beginOp
    BY <1>1, <1>5, <1>6, <2>2
  <2>3. CASE op = bodyOp
    BY <1>5, <2>3
  <2>. QED
    BY <1>4, <2>1, <2>2, <2>3
<1>16. OrderOK'
  <2> DEFINE T == S \cup {beginOp, bodyOp}
  <2>1. <<beginOp, bodyOp>> \in Seq(T)
    BY PairSeq, SeqMonotonic
  <2>2. \A ii \in DOMAIN txnHistory : txnHistory'[ii] = txnHistory[ii]
    BY <1>1, <1>2, <2>1, ConcatProperties, LenProperties
  <2>3. txnHistory'[Len(txnHistory)+1] = beginOp
    BY <1>1, <1>2, <2>1, ConcatProperties, LenProperties
  <2>4. txnHistory'[Len(txnHistory)+2] = bodyOp
    BY <1>1, <1>2, <2>1, ConcatProperties, LenProperties
  <2>5. \A i, j \in DOMAIN txnHistory' :
           txnHistory'[i].txnId = txnHistory'[j].txnId
           /\ txnHistory'[i].type = "begin"
           /\ txnHistory'[j].type \in {"body", "commit", "abort"}
           => i < j
    <3> SUFFICES ASSUME NEW i \in DOMAIN txnHistory', NEW j \in DOMAIN txnHistory',
                        txnHistory'[i].txnId = txnHistory'[j].txnId,
                        txnHistory'[i].type = "begin",
                        txnHistory'[j].type \in {"body", "commit", "abort"}
                 PROVE  i < j
      OBVIOUS
    <3>1. CASE i \in DOMAIN txnHistory /\ j \in DOMAIN txnHistory
      BY <2>2, <3>1 DEF Inv, OrderOK
    <3>2. CASE i \in DOMAIN txnHistory /\ j \notin DOMAIN txnHistory
      <4>1. txnHistory'[i] = txnHistory[i]
        BY <2>2, <3>2
      <4>2. txnHistory[i] \in Range(txnHistory)
        BY <3>2 DEF Range
      <4>3. j = Len(txnHistory)+1 \/ j = Len(txnHistory)+2
        BY <1>1, <1>2, <1>3, <3>2, NewConcatIndex
      <4>4. txnHistory'[j].txnId = tid
        BY <4>3, <1>5, <2>3, <2>4
      <4>5. txnHistory[i].txnId = tid
        BY <4>1, <4>4
      <4>. QED
        BY <1>7, <4>2, <4>5
    <3>3. CASE i \notin DOMAIN txnHistory
      <4>1. i = Len(txnHistory)+1 \/ i = Len(txnHistory)+2
        BY <1>1, <1>2, <1>3, <3>3, NewConcatIndex
      <4>2. i # Len(txnHistory)+2
        BY <1>5, <2>4
      <4>3. i = Len(txnHistory)+1
        BY <4>1, <4>2
      <4>4. CASE j \in DOMAIN txnHistory
        <5>1. txnHistory'[j] \in Range(txnHistory)
          BY <2>2, <4>4 DEF Range
        <5>2. txnHistory'[j].txnId = tid
          BY <1>5, <2>3, <4>3
        <5>. QED
          BY <1>7, <5>1, <5>2
      <4>5. CASE j = Len(txnHistory)+2
        <5>1. Len(txnHistory) \in Nat
          BY <1>2, LenProperties
        <5>. QED
          BY <4>3, <4>5, <5>1
      <4>6. j \in DOMAIN txnHistory \/ j = Len(txnHistory)+2
        BY <1>1, <1>2, ConcatProperties, LenProperties
      <4>. QED
        BY <4>4, <4>5, <4>6
    <3>. QED
      BY <3>1, <3>2, <3>3
  <2>6. \A i, j \in DOMAIN txnHistory' :
           txnHistory'[i].txnId = txnHistory'[j].txnId
           /\ txnHistory'[i].type = "body"
           /\ txnHistory'[j].type \in {"commit", "abort"}
           => i < j
    <3> SUFFICES ASSUME NEW i \in DOMAIN txnHistory', NEW j \in DOMAIN txnHistory',
                        txnHistory'[i].txnId = txnHistory'[j].txnId,
                        txnHistory'[i].type = "body",
                        txnHistory'[j].type \in {"commit", "abort"}
                 PROVE  i < j
      OBVIOUS
    <3>1. CASE i \in DOMAIN txnHistory /\ j \in DOMAIN txnHistory
      BY <2>2, <3>1 DEF Inv, OrderOK
    <3>2. CASE j \notin DOMAIN txnHistory
      <4>1. j = Len(txnHistory)+1 \/ j = Len(txnHistory)+2
        BY <1>1, <1>2, <1>3, <3>2, NewConcatIndex
      <4>2. txnHistory'[j].type \in {"begin", "body"}
        BY <4>1, <1>5, <2>3, <2>4
      <4>. QED
        BY <4>2
    <3>3. CASE i \notin DOMAIN txnHistory /\ j \in DOMAIN txnHistory
      <4>1. txnHistory'[j] \in Range(txnHistory)
        BY <2>2, <3>3 DEF Range
      <4>2. i = Len(txnHistory)+1 \/ i = Len(txnHistory)+2
        BY <1>1, <1>2, <1>3, <3>3, NewConcatIndex
      <4>3. txnHistory'[i].txnId = tid
        BY <4>2, <1>5, <2>3, <2>4
      <4>. QED
        BY <1>7, <4>1, <4>3
    <3>. QED
      BY <3>1, <3>2, <3>3
  <2>. QED
    BY <2>5, <2>6 DEF OrderOK
<1>17. CommitHasPreds'
  <2> SUFFICES ASSUME NEW c \in Range(txnHistory'), c.type = "commit"
               PROVE  /\ \E b \in Range(txnHistory') : b.type = "begin" /\ b.txnId = c.txnId
                      /\ \E d \in Range(txnHistory') : d.type = "body"  /\ d.txnId = c.txnId
    BY DEF CommitHasPreds
  <2>1. c \in Range(txnHistory)
    BY <1>4, <1>5
  <2>. QED
    BY <1>4, <2>1 DEF Inv, CommitHasPreds
<1>18. AbortHasPreds'
  <2> SUFFICES ASSUME NEW a \in Range(txnHistory'), a.type = "abort"
               PROVE  /\ \E b \in Range(txnHistory') : b.type = "begin" /\ b.txnId = a.txnId
                      /\ \E d \in Range(txnHistory') : d.type = "body"  /\ d.txnId = a.txnId
    BY DEF AbortHasPreds
  <2>1. a \in Range(txnHistory)
    BY <1>4, <1>5
  <2>. QED
    BY <1>4, <2>1 DEF Inv, AbortHasPreds
<1>19. H1inv'
  <2> SUFFICES ASSUME NEW b \in Range(txnHistory'), NEW c \in Range(txnHistory'),
                      b.type = "begin", c.type = "commit", b.txnId = c.txnId
               PROVE  b.time < c.time
    BY DEF H1inv
  <2>1. b \in Range(txnHistory) \cup {beginOp} /\ c \in Range(txnHistory)
    BY <1>4, <1>5
  <2>2. CASE b \in Range(txnHistory)
    BY <2>1, <2>2 DEF Inv, H1inv
  <2>3. CASE b = beginOp
    <3>1. c.txnId = tid
      BY <1>5, <2>3
    <3>. QED
      BY <1>7, <2>1, <3>1
  <2>. QED
    BY <2>1, <2>2, <2>3
<1>20. H2inv'
  <2> SUFFICES ASSUME NEW d \in Range(txnHistory'), d.type = "body"
               PROVE  BodyH2(d)
    BY DEF H2inv
  <2>1. CASE d \in Range(txnHistory)
    BY <2>1 DEF Inv, H2inv
  <2>2. CASE d = bodyOp
    <3>1. BodyH2(bodyOp)
      BY <1>5, <1>8 DEF BodyH2
    <3>. QED
      BY <2>2, <3>1
  <2>. QED
    BY <1>4, <2>1, <2>2
<1>21. NoWriteROinv'
  <2> SUFFICES ASSUME NEW op \in Range(txnHistory'), op.type = "body",
                      NEW w \in op.writes
               PROVE  ~ReadOnlyCol(w.key)
    BY DEF NoWriteROinv, NoWriteRO
  <2>1. CASE op \in Range(txnHistory)
    BY <2>1 DEF Inv, NoWriteROinv, NoWriteRO
  <2>2. CASE op = bodyOp
    BY <1>5, <2>2, WorkloadNoROWrite
  <2>. QED
    BY <1>4, <2>1, <2>2
<1>22. H3inv'
  <2> SUFFICES ASSUME NEW c1 \in Range(txnHistory'), NEW c2 \in Range(txnHistory'),
                      c1.type = "commit", c2.type = "commit",
                      c1.txnId # c2.txnId,
                      SI!KeysWrittenByTxn(txnHistory', c1.txnId)
                        \cap SI!KeysWrittenByTxn(txnHistory', c2.txnId) # {},
                      NEW b1 \in Range(txnHistory'), NEW b2 \in Range(txnHistory'),
                      b1.type = "begin", b1.txnId = c1.txnId,
                      b2.type = "begin", b2.txnId = c2.txnId
               PROVE  c1.time < b2.time \/ c2.time < b1.time
    BY DEF H3inv
  <2>1. c1 \in Range(txnHistory) /\ c2 \in Range(txnHistory)
    BY <1>4, <1>5
  <2>2. c1.txnId # tid /\ c2.txnId # tid
    BY <1>7, <2>1
  <2>3. SI!KeysWrittenByTxn(txnHistory', c1.txnId) = SI!KeysWrittenByTxn(txnHistory, c1.txnId)
    BY <1>1, <1>2, <1>5, <2>2, KeysWrittenUnchangedConcatOther
  <2>4. SI!KeysWrittenByTxn(txnHistory', c2.txnId) = SI!KeysWrittenByTxn(txnHistory, c2.txnId)
    BY <1>1, <1>2, <1>5, <2>2, KeysWrittenUnchangedConcatOther
  <2>5. CASE b1 \in Range(txnHistory) /\ b2 \in Range(txnHistory)
    BY <2>1, <2>3, <2>4, <2>5 DEF Inv, H3inv
  <2>6. CASE b1 = beginOp
    BY <1>5, <2>2, <2>6
  <2>7. CASE b2 = beginOp
    BY <1>5, <2>2, <2>7
  <2>8. CASE b1 = bodyOp
    BY <1>5, <2>8
  <2>9. CASE b2 = bodyOp
    BY <1>5, <2>9
  <2>. QED
    BY <1>4, <2>5, <2>6, <2>7, <2>8, <2>9
<1>23. CommitKeys'
  <2> SUFFICES ASSUME NEW c \in Range(txnHistory'), c.type = "commit"
               PROVE  c.updatedKeys = SI!KeysWrittenByTxn(txnHistory', c.txnId)
    BY DEF CommitKeys
  <2>1. c \in Range(txnHistory)
    BY <1>4, <1>5
  <2>2. c.txnId # tid
    BY <1>7, <2>1
  <2>3. c.updatedKeys = SI!KeysWrittenByTxn(txnHistory, c.txnId)
    BY <2>1 DEF Inv, CommitKeys
  <2>4. SI!KeysWrittenByTxn(txnHistory', c.txnId) = SI!KeysWrittenByTxn(txnHistory, c.txnId)
    BY <1>1, <1>2, <1>5, <2>2, KeysWrittenUnchangedConcatOther
  <2>. QED
    BY <2>3, <2>4
<1>24. RunningOK'
  <2>1. newTxn \in [id : TxnIds, startTime : Nat, commitTime : {Empty}]
    BY <1>6
  <2>2. runningTxns' \subseteq [id : TxnIds, startTime : Nat, commitTime : {Empty}]
    BY <1>1, <2>1 DEF Inv, RunningOK
  <2>3. \A txn \in runningTxns' :
           /\ \E b \in Range(txnHistory') :
                 b.type = "begin" /\ b.txnId = txn.id /\ b.time = txn.startTime
           /\ \E d \in Range(txnHistory') : d.type = "body" /\ d.txnId = txn.id
           /\ ~\E c \in Range(txnHistory') : c.type \in {"commit", "abort"} /\ c.txnId = txn.id
    <3> SUFFICES ASSUME NEW txn \in runningTxns'
                 PROVE  /\ \E b \in Range(txnHistory') :
                              b.type = "begin" /\ b.txnId = txn.id /\ b.time = txn.startTime
                        /\ \E d \in Range(txnHistory') : d.type = "body" /\ d.txnId = txn.id
                        /\ ~\E c \in Range(txnHistory') : c.type \in {"commit", "abort"} /\ c.txnId = txn.id
      OBVIOUS
    <3>1. CASE txn \in runningTxns
      <4>1. txn.id # tid
        BY <1>7, <3>1 DEF Inv, RunningOK
      <4>2. \E b \in Range(txnHistory) :
              b.type = "begin" /\ b.txnId = txn.id /\ b.time = txn.startTime
            /\ \E d \in Range(txnHistory) : d.type = "body" /\ d.txnId = txn.id
            /\ ~\E c \in Range(txnHistory) : c.type \in {"commit", "abort"} /\ c.txnId = txn.id
        BY <3>1, RunningHasBeginBody
      <4>3. ~\E c \in Range(txnHistory') : c.type \in {"commit", "abort"} /\ c.txnId = txn.id
        BY <1>4, <1>5, <4>1, <4>2
      <4>. QED
        BY <1>4, <4>2, <4>3
    <3>2. CASE txn = newTxn
      <4>1. beginOp \in Range(txnHistory') /\ bodyOp \in Range(txnHistory')
        BY <1>4
      <4>2. ~\E c \in Range(txnHistory') : c.type \in {"commit", "abort"} /\ c.txnId = tid
        BY <1>4, <1>5, <1>7
      <4>. QED
        BY <1>5, <3>2, <4>1, <4>2
    <3>. QED
      BY <1>1, <3>1, <3>2
  <2>4. \A t1, t2 \in runningTxns' : t1.id = t2.id => t1 = t2
    <3> SUFFICES ASSUME NEW t1 \in runningTxns', NEW t2 \in runningTxns', t1.id = t2.id
                 PROVE  t1 = t2
      OBVIOUS
    <3>1. CASE t1 \in runningTxns /\ t2 \in runningTxns
      BY <3>1 DEF Inv, RunningOK
    <3>2. CASE t1 = newTxn
      <4>1. t2.id = tid
        BY <3>2
      <4>2. t2 \notin runningTxns
        BY <1>7, <4>1 DEF Inv, RunningOK
      <4>. QED
        BY <1>1, <3>2, <4>2
    <3>3. CASE t2 = newTxn
      <4>1. t1.id = tid
        BY <3>3
      <4>2. t1 \notin runningTxns
        BY <1>7, <4>1 DEF Inv, RunningOK
      <4>. QED
        BY <1>1, <3>3, <4>2
    <3>. QED
      BY <1>1, <3>1, <3>2, <3>3
  <2>. QED
    BY <2>2, <2>3, <2>4 DEF RunningOK
<1>. QED
  BY <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18,
     <1>19, <1>20, <1>21, <1>22, <1>23, <1>24
  DEF Inv

-----------------------------------------------------------------------------
(*****************************************************************************)
(* 13. Next and assembly                                                     *)
(*****************************************************************************)

LEMMA NextInv ==
  ASSUME Inv, Next
  PROVE  Inv'
<1>1. CASE \E tid \in TxnIds, req \in Requests : StartAndRun(tid, req)
  BY <1>1, StartInv
<1>2. CASE \E tid \in TxnIds : CommitTxn(tid)
  BY <1>2, CommitInv
<1>3. CASE \E tid \in TxnIds : AbortTxn(tid)
  BY <1>3, AbortInv
<1>4. CASE AllTxnsDone /\ UNCHANGED vars
  BY <1>4, UnchangedInv
<1>. QED
  BY <1>1, <1>2, <1>3, <1>4 DEF Next

LEMMA InvInductive ==
  ASSUME Inv, [Next]_vars
  PROVE  Inv'
<1>1. CASE Next
  BY <1>1, NextInv
<1>2. CASE UNCHANGED vars
  BY <1>2, UnchangedInv
<1>. QED
  BY <1>1, <1>2

THEOREM Safety == Spec => []SerializableViaPath
<1>1. Init => Inv
  BY InitInv
<1>2. Inv /\ [Next]_vars => Inv'
  BY InvInductive
<1>3. Inv => SerializableViaPath
  BY InvSerializable
<1>. QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec

=============================================================================

