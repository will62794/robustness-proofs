----------------------------- MODULE Auction_Proofs -----------------------------
(*****************************************************************************)
(* TLAPS proof that every history of the StoreBid + ViewItem mix is          *)
(* conflict serializable:                                                    *)
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
(*   H2  an updater reads only keys it also writes   (the workload)          *)
(*   H3  two committed writers of a common key have disjoint lifetimes (FCW) *)
(*                                                                           *)
(* H2 is exactly what separates the paper's two analyses: StoreBid reads     *)
(* ITEM(i) and writes ITEM(i); ViewItem writes nothing.  RegUser scans every *)
(* USERS key and writes one, so it is excluded by RobustMix.                 *)
(*****************************************************************************)

EXTENDS Auction, NaturalsInduction, SequenceTheorems, FiniteSetTheorems, TLAPS

\* The mix the CONCUR'16 paper proves robust under SI / PSI.
ASSUME RobustMix == EnabledTxnTypes \subseteq {"StoreBid", "ViewItem"}

ASSUME NumItemsNat == NumItems \in Nat
ASSUME NumUsersNat == NumUsers \in Nat
ASSUME NumNamesNat == NumNames \in Nat

-----------------------------------------------------------------------------
(*****************************************************************************)
(* 1.  Empty history                                                         *)
(*****************************************************************************)

LEMMA RangeEq == \A f : Range(f) = SI!Range(f)
BY DEF Range, SI!Range

LEMMA EmptyRange == Range(<<>>) = {}
<1>1. <<>> \in Seq({})
  BY EmptySeq
<1>2. Len(<<>>) = 0
  BY EmptySeq
<1>3. Range(<<>>) = { <<>>[i] : i \in 1..Len(<<>>) }
  BY <1>1, RangeEquality
<1>4. 1..0 = {}
  OBVIOUS
<1>. QED
  BY <1>2, <1>3, <1>4

LEMMA EmptyCommitted == SI!CommittedTxns(<<>>) = {}
<1>1. Range(<<>>) = {}
  BY EmptyRange
<1>2. SI!Range(<<>>) = {}
  BY <1>1, RangeEq
<1>. QED
  BY <1>2 DEF SI!CommittedTxns

LEMMA EmptyGraph == SI!SerializationGraph(<<>>) = {}
<1>1. SI!CommittedTxns(<<>>) = {}
  BY EmptyCommitted
<1>2. SI!CommittedTxns(<<>>) \X SI!CommittedTxns(<<>>) = {}
  BY <1>1
<1>. QED
  BY <1>1, <1>2 DEF SI!SerializationGraph

LEMMA EmptyGraphNodes == SI!GraphNodes({}) = {}
BY DEF SI!GraphNodes

LEMMA FunEmptyCodomain ==
  ASSUME NEW S, S # {}
  PROVE  [S -> {}] = {}
<1>. SUFFICES ASSUME NEW f \in [S -> {}] PROVE FALSE
  OBVIOUS
<1>. PICK x \in S : TRUE
  OBVIOUS
<1>. f[x] \in {}
  OBVIOUS
<1>. QED
  OBVIOUS

LEMMA PathConsecutive ==
  ASSUME NEW edges, NEW p \in SI!Paths(edges)
  PROVE  \A i \in 1..(Len(p)-1) : <<p[i], p[i+1]>> \in edges
BY DEF SI!Paths

LEMMA EmptyNoCycle == ~SI!IsCycleViaPath({})
<1> SUFFICES ASSUME NEW p \in SI!Paths({}), Len(p) > 1, p[1] = p[Len(p)]
             PROVE FALSE
  BY DEF SI!IsCycleViaPath
<1>1. \A i \in 1..(Len(p)-1) : <<p[i], p[i+1]>> \in {}
  BY PathConsecutive
<1>2. <<p[1], p[2]>> \in {}
  BY <1>1
<1>. QED
  BY <1>2

LEMMA EmptySerializable == SI!IsConflictSerializableViaPath(<<>>)
BY EmptyGraph, EmptyNoCycle DEF SI!IsConflictSerializableViaPath

-----------------------------------------------------------------------------
(*****************************************************************************)
(* 2.  A strictly ranked graph has no cycle                                  *)
(*****************************************************************************)

\* Consecutive edges of a sequence strictly raise an integer rank, so the
\* first node of a path of length >= 2 has smaller rank than the last.
LEMMA RankAlongSeq ==
  ASSUME NEW edges,
         NEW r(_),
         \A e \in edges : r(e[1]) \in Nat /\ r(e[2]) \in Nat /\ r(e[1]) < r(e[2]),
         NEW T, NEW p \in Seq(T),
         Len(p) >= 2,
         \A i \in 1..(Len(p)-1) : <<p[i], p[i+1]>> \in edges
  PROVE  r(p[1]) < r(p[Len(p)])
<1>1. Len(p) \in Nat
  BY LenProperties
<1>2. Len(p) - 1 \in Nat
  BY <1>1
<1> DEFINE Q(n) == n \in 1..(Len(p)-1) => r(p[1]) < r(p[n+1])
<1>3. Q(0)
  BY DEF Q
<1>4. \A n \in Nat : Q(n) => Q(n+1)
  <2> SUFFICES ASSUME NEW n \in Nat, Q(n), n+1 \in 1..(Len(p)-1)
               PROVE  r(p[1]) < r(p[n+2])
    BY DEF Q
  <2>1. CASE n = 0
    <3>1. <<p[1], p[2]>> \in edges
      OBVIOUS
    <3>. QED
      BY <2>1, <3>1
  <2>2. CASE n # 0
    <3>1. n \in 1..(Len(p)-1)
      BY <1>1, <1>2, <2>2
    <3>2. r(p[1]) < r(p[n+1])
      BY <3>1 DEF Q
    <3>3. <<p[n+1], p[n+2]>> \in edges
      OBVIOUS
    <3>4. r(p[n+1]) \in Nat /\ r(p[n+2]) \in Nat /\ r(p[n+1]) < r(p[n+2])
      BY <3>3
    <3>5. <<p[1], p[2]>> \in edges
      OBVIOUS
    <3>6. r(p[1]) \in Nat
      BY <3>5
    <3>. QED
      BY <3>2, <3>4, <3>6
  <2>. QED
    BY <2>1, <2>2
<1>5. \A n \in Nat : Q(n)
  BY <1>3, <1>4, NatInduction, Isa
<1>6. Len(p)-1 \in 1..(Len(p)-1)
  BY <1>1, <1>2
<1>7. Q(Len(p)-1)
  BY <1>5, <1>2
<1>. QED
  BY <1>6, <1>7 DEF Q

LEMMA PathProperties ==
  ASSUME NEW edges,
         NEW p \in SI!Paths(edges)
  PROVE  /\ p \in Seq(SI!GraphNodes(edges))
         /\ Len(p) \in Nat
         /\ Len(p) >= 1
         /\ \A i \in 1..(Len(p)-1) : <<p[i], p[i+1]>> \in edges
<1> DEFINE nodes == SI!GraphNodes(edges)
<1>1. \A i \in 1..(Len(p)-1) : <<p[i], p[i+1]>> \in edges
  BY PathConsecutive
<1>2. p \in UNION {[1..n -> nodes] : n \in 1..SI!PathBound(edges)}
  BY DEF SI!Paths
<1>3. PICK n \in 1..SI!PathBound(edges) : p \in [1..n -> nodes]
  BY <1>2
<1>4. n \in Int /\ n >= 1
  OBVIOUS
<1>5. n \in Nat
  BY <1>4
<1>6. p \in Seq(nodes)
  BY <1>3, <1>5, SeqDef
<1>7. Len(p) = n
  BY <1>3, <1>5, <1>6, LenProperties
<1>8. Len(p) >= 1
  BY <1>4, <1>7
<1>. QED
  BY <1>1, <1>6, <1>7, <1>8, LenProperties

LEMMA RankedNoCycle ==
  ASSUME NEW edges,
         NEW r(_),
         \A e \in edges : r(e[1]) \in Nat /\ r(e[2]) \in Nat /\ r(e[1]) < r(e[2])
  PROVE  ~SI!IsCycleViaPath(edges)
<1> SUFFICES ASSUME SI!IsCycleViaPath(edges) PROVE FALSE
  OBVIOUS
<1>1. PICK p \in SI!Paths(edges) : Len(p) > 1 /\ p[1] = p[Len(p)]
  BY DEF SI!IsCycleViaPath
<1>2. /\ p \in Seq(SI!GraphNodes(edges))
      /\ Len(p) \in Nat
      /\ Len(p) >= 1
      /\ \A i \in 1..(Len(p)-1) : <<p[i], p[i+1]>> \in edges
  BY <1>1, PathProperties
<1>3. Len(p) >= 2
  BY <1>1, <1>2
<1>4. r(p[1]) < r(p[Len(p)])
  BY <1>2, <1>3, RankAlongSeq
<1>5. r(p[1]) = r(p[Len(p)])
  BY <1>1
<1>. QED
  BY <1>4, <1>5

-----------------------------------------------------------------------------
(*****************************************************************************)
(* 3.  H1–H3 make every MVSG edge increase rank                              *)
(*****************************************************************************)

HasBegin(h, t) == \E op \in Range(h) : op.txnId = t /\ op.type = "begin"
HasCommit(h, t) == \E op \in Range(h) : op.txnId = t /\ op.type = "commit"
HasBody(h, t) == \E op \in Range(h) : op.txnId = t /\ op.type = "body"

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
    /\ HasBegin(h, t)
    /\ HasCommit(h, t)
    /\ HasBody(h, t)

H1(h) ==
  \A t \in SI!CommittedTxns(h) :
    SI!BeginOp(h, t).time < SI!CommitOp(h, t).time

H2(h) ==
  \A t \in SI!CommittedTxns(h) :
    SI!KeysWrittenByTxn(h, t) # {} =>
      SI!KeysReadByTxn(h, t) \subseteq SI!KeysWrittenByTxn(h, t)

H3(h) ==
  \A t1, t2 \in SI!CommittedTxns(h) :
    t1 # t2 =>
    (SI!KeysWrittenByTxn(h, t1) \cap SI!KeysWrittenByTxn(h, t2) # {} =>
       SI!CommitOp(h, t1).time < SI!BeginOp(h, t2).time
       \/ SI!CommitOp(h, t2).time < SI!BeginOp(h, t1).time)

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
  PROVE  /\ (CHOOSE x \in S : P(x)) \in S
         /\ P(CHOOSE x \in S : P(x))
<1> PICK y \in S : P(y)
  OBVIOUS
<1>1. P(CHOOSE x \in S : P(x))
  OBVIOUS
<1>2. (CHOOSE x \in S : P(x)) \in S
  OBVIOUS
<1>. QED
  BY <1>1, <1>2

LEMMA ChooseBegin ==
  ASSUME NEW h, NEW t, HasBegin(h, t)
  PROVE  /\ SI!BeginOp(h, t) \in Range(h)
         /\ SI!BeginOp(h, t).txnId = t
         /\ SI!BeginOp(h, t).type = "begin"
<1> DEFINE P(op) == op.txnId = t /\ op.type = "begin"
<1>1. \E op \in SI!Range(h) : P(op)
  BY RangeEq DEF HasBegin, P
<1>2. (CHOOSE op \in SI!Range(h) : P(op)) \in SI!Range(h)
      /\ P(CHOOSE op \in SI!Range(h) : P(op))
  BY <1>1, ChooseExists
<1>3. SI!BeginOp(h, t) = CHOOSE op \in SI!Range(h) : P(op)
  BY DEF SI!BeginOp, P
<1>. QED
  BY <1>2, <1>3, RangeEq DEF P

LEMMA ChooseCommit ==
  ASSUME NEW h, NEW t, HasCommit(h, t)
  PROVE  /\ SI!CommitOp(h, t) \in Range(h)
         /\ SI!CommitOp(h, t).txnId = t
         /\ SI!CommitOp(h, t).type = "commit"
<1> DEFINE P(op) == op.txnId = t /\ op.type = "commit"
<1>1. \E op \in SI!Range(h) : P(op)
  BY RangeEq DEF HasCommit, P
<1>2. (CHOOSE op \in SI!Range(h) : P(op)) \in SI!Range(h)
      /\ P(CHOOSE op \in SI!Range(h) : P(op))
  BY <1>1, ChooseExists
<1>3. SI!CommitOp(h, t) = CHOOSE op \in SI!Range(h) : P(op)
  BY DEF SI!CommitOp, P
<1>. QED
  BY <1>2, <1>3, RangeEq DEF P

LEMMA BeginOpUnique ==
  ASSUME NEW h, UniqueBegin(h), NEW t, HasBegin(h, t),
         NEW b \in Range(h), b.txnId = t, b.type = "begin"
  PROVE  SI!BeginOp(h, t) = b
<1>1. SI!BeginOp(h, t) \in Range(h)
      /\ SI!BeginOp(h, t).txnId = t
      /\ SI!BeginOp(h, t).type = "begin"
  BY ChooseBegin
<1>. QED
  BY <1>1 DEF UniqueBegin

LEMMA CommitOpUnique ==
  ASSUME NEW h, UniqueCommit(h), NEW t, HasCommit(h, t),
         NEW c \in Range(h), c.txnId = t, c.type = "commit"
  PROVE  SI!CommitOp(h, t) = c
<1>1. SI!CommitOp(h, t) \in Range(h)
      /\ SI!CommitOp(h, t).txnId = t
      /\ SI!CommitOp(h, t).type = "commit"
  BY ChooseCommit
<1>. QED
  BY <1>1 DEF UniqueCommit

LEMMA RankType ==
  ASSUME NEW h, HistFacts(h),
         NEW t \in SI!CommittedTxns(h)
  PROVE  Rank(h, t) \in Nat
<1>1. HasBegin(h, t) /\ HasCommit(h, t)
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
  ASSUME NEW h, HistFacts(h),
         NEW t \in SI!CommittedTxns(h)
  PROVE  SI!BeginOp(h, t).time \in Nat
<1>1. HasBegin(h, t)
  BY DEF HistFacts, CommittedOK
<1>2. SI!BeginOp(h, t) \in Range(h) /\ SI!BeginOp(h, t).type = "begin"
  BY <1>1, ChooseBegin
<1>. QED
  BY <1>2 DEF HistFacts, TimedOpsOK

LEMMA CommitTimeType ==
  ASSUME NEW h, HistFacts(h),
         NEW t \in SI!CommittedTxns(h)
  PROVE  SI!CommitOp(h, t).time \in Nat
<1>1. HasCommit(h, t)
  BY DEF HistFacts, CommittedOK
<1>2. SI!CommitOp(h, t) \in Range(h) /\ SI!CommitOp(h, t).type = "commit"
  BY <1>1, ChooseCommit
<1>. QED
  BY <1>2 DEF HistFacts, TimedOpsOK

LEMMA WroteMeansNonempty ==
  ASSUME NEW h, NEW t, NEW k \in Keys,
         SI!WritesKey(h, t, k)
  PROVE  SI!KeysWrittenByTxn(h, t) # {}
BY DEF SI!KeysWrittenByTxn

LEMMA WWEdgesRank ==
  ASSUME NEW h, HistFacts(h),
         NEW t1 \in SI!CommittedTxns(h),
         NEW t2 \in SI!CommittedTxns(h),
         SI!WWDependency(h, t1, t2)
  PROVE  Rank(h, t1) < Rank(h, t2)
<1>1. PICK k \in Keys : SI!WritesKey(h, t1, k) /\ SI!WritesKey(h, t2, k)
  BY DEF SI!WWDependency
<1>2. SI!KeysWrittenByTxn(h, t1) # {} /\ SI!KeysWrittenByTxn(h, t2) # {}
  BY <1>1, WroteMeansNonempty
<1>3. Rank(h, t1) = SI!CommitOp(h, t1).time
  BY <1>2 DEF Rank
<1>4. Rank(h, t2) = SI!CommitOp(h, t2).time
  BY <1>2 DEF Rank
<1>5. SI!CommitOp(h, t1).time < SI!CommitOp(h, t2).time
  BY DEF SI!WWDependency
<1>. QED
  BY <1>3, <1>4, <1>5

LEMMA WREdgesRank ==
  ASSUME NEW h, HistFacts(h),
         NEW t1 \in SI!CommittedTxns(h),
         NEW t2 \in SI!CommittedTxns(h),
         SI!WRDependency(h, t1, t2)
  PROVE  Rank(h, t1) < Rank(h, t2)
<1>1. PICK k \in Keys : SI!WritesKey(h, t1, k) /\ SI!ReadsKey(h, t2, k)
  BY DEF SI!WRDependency
<1>2. SI!KeysWrittenByTxn(h, t1) # {}
  BY <1>1, WroteMeansNonempty
<1>3. Rank(h, t1) = SI!CommitOp(h, t1).time
  BY <1>2 DEF Rank
<1>4. SI!CommitOp(h, t1).time < SI!BeginOp(h, t2).time
  BY DEF SI!WRDependency
<1>5. SI!BeginOp(h, t2).time \in Nat /\ SI!CommitOp(h, t1).time \in Nat
  BY BeginTimeType, CommitTimeType
<1>6. CASE SI!KeysWrittenByTxn(h, t2) = {}
  <2>1. Rank(h, t2) = SI!BeginOp(h, t2).time
    BY <1>6 DEF Rank
  <2>. QED
    BY <1>3, <1>4, <2>1
<1>7. CASE SI!KeysWrittenByTxn(h, t2) # {}
  <2>1. Rank(h, t2) = SI!CommitOp(h, t2).time
    BY <1>7 DEF Rank
  <2>2. SI!BeginOp(h, t2).time < SI!CommitOp(h, t2).time
    BY DEF HistFacts, H1
  <2>3. SI!CommitOp(h, t2).time \in Nat
    BY CommitTimeType
  <2>. QED
    BY <1>3, <1>4, <1>5, <2>1, <2>2, <2>3
<1>. QED
  BY <1>6, <1>7

LEMMA RWEdgesRank ==
  ASSUME NEW h, HistFacts(h),
         NEW t1 \in SI!CommittedTxns(h),
         NEW t2 \in SI!CommittedTxns(h),
         t1 # t2,
         SI!RWDependency(h, t1, t2)
  PROVE  Rank(h, t1) < Rank(h, t2)
<1>1. PICK k \in Keys : SI!ReadsKey(h, t1, k) /\ SI!WritesKey(h, t2, k)
  BY DEF SI!RWDependency
<1>2. SI!KeysWrittenByTxn(h, t2) # {}
  BY <1>1, WroteMeansNonempty
<1>3. Rank(h, t2) = SI!CommitOp(h, t2).time
  BY <1>2 DEF Rank
<1>4. SI!BeginOp(h, t1).time < SI!CommitOp(h, t2).time
  BY DEF SI!RWDependency
<1>5. SI!BeginOp(h, t1).time \in Nat /\ SI!CommitOp(h, t2).time \in Nat
  BY BeginTimeType, CommitTimeType
<1>6. CASE SI!KeysWrittenByTxn(h, t1) = {}
  <2>1. Rank(h, t1) = SI!BeginOp(h, t1).time
    BY <1>6 DEF Rank
  <2>. QED
    BY <1>3, <1>4, <2>1
<1>7. CASE SI!KeysWrittenByTxn(h, t1) # {}
  <2>1. Rank(h, t1) = SI!CommitOp(h, t1).time
    BY <1>7 DEF Rank
  <2>2. k \in SI!KeysReadByTxn(h, t1)
    BY <1>1 DEF SI!KeysReadByTxn
  <2>3. SI!KeysReadByTxn(h, t1) \subseteq SI!KeysWrittenByTxn(h, t1)
    BY <1>7 DEF HistFacts, H2
  <2>4. k \in SI!KeysWrittenByTxn(h, t1)
    BY <2>2, <2>3
  <2>5. SI!WritesKey(h, t1, k)
    BY <2>4 DEF SI!KeysWrittenByTxn
  <2>6. SI!KeysWrittenByTxn(h, t1) \cap SI!KeysWrittenByTxn(h, t2) # {}
    BY <2>4, <1>1, <1>2 DEF SI!KeysWrittenByTxn
  <2>7. SI!CommitOp(h, t1).time < SI!BeginOp(h, t2).time
        \/ SI!CommitOp(h, t2).time < SI!BeginOp(h, t1).time
    BY <2>6 DEF HistFacts, H3
  <2>8. ~ (SI!CommitOp(h, t2).time < SI!BeginOp(h, t1).time)
    BY <1>4, <1>5
  <2>9. SI!CommitOp(h, t1).time < SI!BeginOp(h, t2).time
    BY <2>7, <2>8
  <2>10. SI!BeginOp(h, t2).time < SI!CommitOp(h, t2).time
    BY DEF HistFacts, H1
  <2>11. SI!CommitOp(h, t1).time \in Nat /\ SI!BeginOp(h, t2).time \in Nat
    BY BeginTimeType, CommitTimeType
  <2>12. SI!CommitOp(h, t1).time < SI!CommitOp(h, t2).time
    BY <2>9, <2>10, <2>11, <1>5
  <2>. QED
    BY <2>1, <1>3, <2>12
<1>. QED
  BY <1>6, <1>7

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
  BY GraphEdgeShape
<1>2. Rank(h, e[1]) \in Nat /\ Rank(h, e[2]) \in Nat
  BY <1>1, RankType
<1>3. CASE SI!WWDependency(h, e[1], e[2])
  BY <1>1, <1>2, <1>3, WWEdgesRank
<1>4. CASE SI!WRDependency(h, e[1], e[2])
  BY <1>1, <1>2, <1>4, WREdgesRank
<1>5. CASE SI!RWDependency(h, e[1], e[2])
  BY <1>1, <1>2, <1>5, RWEdgesRank
<1>. QED
  BY <1>2, <1>3, <1>4, <1>5, GraphEdgeShape

LEMMA GraphNodesCommitted ==
  ASSUME NEW h
  PROVE  SI!GraphNodes(SI!SerializationGraph(h)) \subseteq SI!CommittedTxns(h)
<1> SUFFICES ASSUME NEW x \in SI!GraphNodes(SI!SerializationGraph(h))
             PROVE  x \in SI!CommittedTxns(h)
  OBVIOUS
<1>1. PICK e \in SI!SerializationGraph(h) : x = e[1] \/ x = e[2]
  BY DEF SI!GraphNodes
<1>. QED
  BY <1>1, GraphEdgeShape

LEMMA TxnIdsFinite == IsFiniteSet(TxnIds)
<1>1. NumTxns \in Int
  BY NumTxnsNat
<1>2. 1 \in Int
  OBVIOUS
<1>. QED
  BY <1>1, <1>2, FS_Interval DEF TxnIds

LEMMA CommittedFinite ==
  ASSUME NEW h, SI!CommittedTxns(h) \subseteq TxnIds
  PROVE  IsFiniteSet(SI!CommittedTxns(h))
BY TxnIdsFinite, FS_Subset

LEMMA GraphNodesFinite ==
  ASSUME NEW h, SI!CommittedTxns(h) \subseteq TxnIds
  PROVE  IsFiniteSet(SI!GraphNodes(SI!SerializationGraph(h)))
BY GraphNodesCommitted, CommittedFinite, FS_Subset

LEMMA HistFactsSerializable ==
  ASSUME NEW h, HistFacts(h)
  PROVE  SI!IsConflictSerializableViaPath(h)
<1>1. \A e \in SI!SerializationGraph(h) :
         Rank(h, e[1]) \in Nat /\ Rank(h, e[2]) \in Nat /\ Rank(h, e[1]) < Rank(h, e[2])
  BY EdgesIncreaseRank
<1>2. ~SI!IsCycleViaPath(SI!SerializationGraph(h))
  BY <1>1, RankedNoCycle
<1>. QED
  BY <1>2 DEF SI!IsConflictSerializableViaPath

-----------------------------------------------------------------------------
(*****************************************************************************)
(* 4.  Workload lemma: StoreBid and ViewItem satisfy H2                      *)
(*****************************************************************************)

LEMMA RequestTypes ==
  ASSUME NEW req \in Requests
  PROVE  req.type \in {"StoreBid", "ViewItem"}
<1>1. EnabledTxnTypes \subseteq {"StoreBid", "ViewItem"}
  BY RobustMix
<1>2. "RegUser" \notin EnabledTxnTypes
  BY <1>1
<1>3. "ViewUsers" \notin EnabledTxnTypes
  BY <1>1
<1>. QED
  BY <1>1, <1>2, <1>3 DEF Requests

LEMMA ProgramForStoreBid ==
  ASSUME NEW tid, NEW req, NEW snap, req.type = "StoreBid"
  PROVE  ProgramFor(tid, req, snap) = StoreBidProgram(tid, req, snap)
BY DEF ProgramFor

LEMMA ProgramForViewItem ==
  ASSUME NEW tid, NEW req, NEW snap, req.type = "ViewItem"
  PROVE  ProgramFor(tid, req, snap) = ViewItemProgram(req, snap)
BY DEF ProgramFor

BodyH2(B) ==
  B.writes = {} \/ \A k \in B.reads : \E w \in B.writes : w.key = k

LEMMA ViewItemH2 ==
  ASSUME NEW req, NEW snap
  PROVE  BodyH2(ViewItemProgram(req, snap))
BY DEF BodyH2, ViewItemProgram

LEMMA StoreBidH2 ==
  ASSUME NEW tid, NEW req, NEW snap
  PROVE  BodyH2(StoreBidProgram(tid, req, snap))
<1> DEFINE B == StoreBidProgram(tid, req, snap)
<1>1. B.reads = {ItemKey(req.iid)}
  BY DEF StoreBidProgram
<1>2. \E w \in B.writes : w.key = ItemKey(req.iid)
  BY DEF StoreBidProgram
<1>. QED
  BY <1>1, <1>2 DEF BodyH2, StoreBidProgram

LEMMA WorkloadH2 ==
  ASSUME NEW tid \in TxnIds,
         NEW req \in Requests,
         NEW snap
  PROVE  BodyH2(ProgramFor(tid, req, snap))
<1>1. req.type = "StoreBid" \/ req.type = "ViewItem"
  BY RequestTypes
<1>2. CASE req.type = "StoreBid"
  <2>1. ProgramFor(tid, req, snap) = StoreBidProgram(tid, req, snap)
    BY <1>2, ProgramForStoreBid
  <2>. QED
    BY <1>2, <2>1, StoreBidH2
<1>3. CASE req.type = "ViewItem"
  <2>1. ProgramFor(tid, req, snap) = ViewItemProgram(req, snap)
    BY <1>3, ProgramForViewItem
  <2>. QED
    BY <1>3, <2>1, ViewItemH2
<1>. QED
  BY <1>1, <1>2, <1>3

LEMMA BodyH2ToKeys ==
  ASSUME NEW h, NEW t,
         NEW d \in Range(h),
         d.type = "body", d.txnId = t,
         UniqueBody(h),
         BodyH2(d),
         d.reads \subseteq Keys,
         \A w \in d.writes : w.key \in Keys
  PROVE  SI!KeysWrittenByTxn(h, t) # {} =>
           SI!KeysReadByTxn(h, t) \subseteq SI!KeysWrittenByTxn(h, t)
<1> SUFFICES ASSUME SI!KeysWrittenByTxn(h, t) # {}
             PROVE  SI!KeysReadByTxn(h, t) \subseteq SI!KeysWrittenByTxn(h, t)
  OBVIOUS
<1>1. PICK k0 \in SI!KeysWrittenByTxn(h, t) : TRUE
  OBVIOUS
<1>2. SI!WritesKey(h, t, k0)
  BY <1>1 DEF SI!KeysWrittenByTxn
<1>3. PICK op \in Range(h) : op.txnId = t /\ op.type = "body" /\ \E w \in op.writes : w.key = k0
  BY <1>2, RangeEq DEF SI!WritesKey
<1>4. op = d
  BY <1>3 DEF UniqueBody
<1>5. d.writes # {}
  BY <1>3, <1>4
<1>6. \A k \in d.reads : \E w \in d.writes : w.key = k
  BY <1>5 DEF BodyH2
<1> SUFFICES ASSUME NEW k \in SI!KeysReadByTxn(h, t)
             PROVE  k \in SI!KeysWrittenByTxn(h, t)
  OBVIOUS
<1>7. SI!ReadsKey(h, t, k)
  BY DEF SI!KeysReadByTxn
<1>8. PICK opR \in Range(h) : opR.txnId = t /\ opR.type = "body" /\ k \in opR.reads
  BY <1>7, RangeEq DEF SI!ReadsKey
<1>9. opR = d
  BY <1>8 DEF UniqueBody
<1>10. k \in d.reads
  BY <1>8, <1>9
<1>11. PICK w \in d.writes : w.key = k
  BY <1>6, <1>10
<1>12. w.key \in Keys
  OBVIOUS
<1>13. k \in Keys
  BY <1>11, <1>12
<1>14. SI!WritesKey(h, t, k)
  BY <1>11, RangeEq DEF SI!WritesKey
<1>. QED
  BY <1>13, <1>14 DEF SI!KeysWrittenByTxn

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

LEMMA SeqIndexLtLenP1 ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW i \in DOMAIN seq
  PROVE  i < Len(seq) + 1
<1>1. DOMAIN seq = 1..Len(seq)
  BY LenProperties
<1>2. Len(seq) \in Nat
  BY LenProperties
<1>3. i \in 1..Len(seq)
  BY <1>1
<1>. QED
  BY <1>2, <1>3

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

LEMMA WritesKeyBodyOnly ==
  ASSUME NEW h, NEW t, NEW k, NEW op \in Range(h),
         SI!WritesKey(h, t, k),
         op.txnId = t /\ op.type = "body",
         UniqueBody(h)
  PROVE  \E w \in op.writes : w.key = k
<1>1. PICK op2 \in Range(h) : op2.txnId = t /\ op2.type = "body" /\ \E w \in op2.writes : w.key = k
  BY RangeEq DEF SI!WritesKey
<1>2. op2 = op
  BY <1>1 DEF UniqueBody
<1>. QED
  BY <1>1, <1>2

LEMMA WritesUnchangedNonBody ==
  ASSUME NEW S, NEW h \in Seq(S), NEW x, x.type # "body"
  PROVE  \A t, k : SI!WritesKey(Append(h, x), t, k) <=> SI!WritesKey(h, t, k)
<1>1. Range(Append(h, x)) = Range(h) \cup {x}
  BY RangeAppend
<1>2. SI!Range(Append(h, x)) = SI!Range(h) \cup {x}
  BY <1>1, RangeEq
<1>. QED
  BY <1>1, <1>2 DEF SI!WritesKey

LEMMA ReadsUnchangedNonBody ==
  ASSUME NEW S, NEW h \in Seq(S), NEW x, x.type # "body"
  PROVE  \A t, k : SI!ReadsKey(Append(h, x), t, k) <=> SI!ReadsKey(h, t, k)
<1>1. Range(Append(h, x)) = Range(h) \cup {x}
  BY RangeAppend
<1>2. SI!Range(Append(h, x)) = SI!Range(h) \cup {x}
  BY <1>1, RangeEq
<1>. QED
  BY <1>1, <1>2 DEF SI!ReadsKey

LEMMA KeysWrittenUnchangedNonBody ==
  ASSUME NEW S, NEW h \in Seq(S), NEW x, x.type # "body"
  PROVE  \A t : SI!KeysWrittenByTxn(Append(h, x), t) = SI!KeysWrittenByTxn(h, t)
BY WritesUnchangedNonBody DEF SI!KeysWrittenByTxn, Keys

LEMMA KeysReadUnchangedNonBody ==
  ASSUME NEW S, NEW h \in Seq(S), NEW x, x.type # "body"
  PROVE  \A t : SI!KeysReadByTxn(Append(h, x), t) = SI!KeysReadByTxn(h, t)
BY ReadsUnchangedNonBody DEF SI!KeysReadByTxn, Keys

LEMMA CommittedAppendCommit ==
  ASSUME NEW S, NEW h \in Seq(S), NEW x, x.type = "commit", "txnId" \in DOMAIN x
  PROVE  SI!CommittedTxns(Append(h, x)) = SI!CommittedTxns(h) \cup {x.txnId}
<1>1. Range(Append(h, x)) = Range(h) \cup {x}
  BY RangeAppend
<1>2. SI!Range(Append(h, x)) = SI!Range(h) \cup {x}
  BY <1>1, RangeEq
<1>. QED
  BY <1>1, <1>2 DEF SI!CommittedTxns

LEMMA CommittedAppendNonCommit ==
  ASSUME NEW S, NEW h \in Seq(S), NEW x, x.type # "commit"
  PROVE  SI!CommittedTxns(Append(h, x)) = SI!CommittedTxns(h)
<1>1. Range(Append(h, x)) = Range(h) \cup {x}
  BY RangeAppend
<1>2. SI!Range(Append(h, x)) = SI!Range(h) \cup {x}
  BY <1>1, RangeEq
<1>. QED
  BY <1>1, <1>2 DEF SI!CommittedTxns

LEMMA CommittedConcatPairNonCommit ==
  ASSUME NEW S, NEW h \in Seq(S), NEW a, NEW b,
         a.type # "commit", b.type # "commit"
  PROVE  SI!CommittedTxns(h \o <<a, b>>) = SI!CommittedTxns(h)
<1>1. Range(h \o <<a, b>>) = Range(h) \cup {a, b}
  BY RangeConcatPair
<1>2. SI!Range(h \o <<a, b>>) = SI!Range(h) \cup {a, b}
  BY <1>1, RangeEq
<1>. QED
  BY <1>1, <1>2 DEF SI!CommittedTxns

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
         /\ op.reads \subseteq Keys
         /\ \A w \in op.writes : "key" \in DOMAIN w /\ w.key \in Keys
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
<1>3. i = j
  BY <1>1, <1>2 DEF Inv, UniqueOps
<1>. QED
  BY <1>1, <1>2, <1>3

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
<1>3. i = j
  BY <1>1, <1>2 DEF Inv, UniqueOps
<1>. QED
  BY <1>1, <1>2, <1>3

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
<1>3. i = j
  BY <1>1, <1>2 DEF Inv, UniqueOps
<1>. QED
  BY <1>1, <1>2, <1>3

LEMMA InvTimedOpsOK ==
  ASSUME Inv
  PROVE  TimedOpsOK(txnHistory)
BY DEF Inv, OpShape, TimedOpsOK

LEMMA InvCommittedSubset ==
  ASSUME Inv
  PROVE  SI!CommittedTxns(txnHistory) \subseteq TxnIds
<1> SUFFICES ASSUME NEW t \in SI!CommittedTxns(txnHistory)
             PROVE  t \in TxnIds
  OBVIOUS
<1>1. PICK op \in SI!Range(txnHistory) : op.txnId = t /\ op.type = "commit"
  BY DEF SI!CommittedTxns
<1>2. op \in Range(txnHistory)
  BY <1>1, RangeEq
<1>3. op.txnId \in TxnIds
  BY <1>2 DEF Inv, OpShape
<1>. QED
  BY <1>1, <1>3

LEMMA InvCommittedOK ==
  ASSUME Inv
  PROVE  CommittedOK(txnHistory)
<1> SUFFICES ASSUME NEW t \in SI!CommittedTxns(txnHistory)
             PROVE  HasBegin(txnHistory, t) /\ HasCommit(txnHistory, t) /\ HasBody(txnHistory, t)
  BY DEF CommittedOK
<1>1. PICK c \in Range(txnHistory) : c.txnId = t /\ c.type = "commit"
  BY RangeEq DEF SI!CommittedTxns
<1>2. HasCommit(txnHistory, t)
  BY <1>1 DEF HasCommit
<1>3. HasBegin(txnHistory, t) /\ HasBody(txnHistory, t)
  BY <1>1 DEF Inv, CommitHasPreds, HasBegin, HasBody
<1>. QED
  BY <1>2, <1>3

LEMMA InvH1 ==
  ASSUME Inv
  PROVE  H1(txnHistory)
<1> SUFFICES ASSUME NEW t \in SI!CommittedTxns(txnHistory)
             PROVE  SI!BeginOp(txnHistory, t).time < SI!CommitOp(txnHistory, t).time
  BY DEF H1
<1>1. HasBegin(txnHistory, t) /\ HasCommit(txnHistory, t)
  BY InvCommittedOK DEF CommittedOK
<1>2. SI!BeginOp(txnHistory, t) \in Range(txnHistory)
      /\ SI!BeginOp(txnHistory, t).type = "begin"
      /\ SI!BeginOp(txnHistory, t).txnId = t
  BY <1>1, ChooseBegin
<1>3. SI!CommitOp(txnHistory, t) \in Range(txnHistory)
      /\ SI!CommitOp(txnHistory, t).type = "commit"
      /\ SI!CommitOp(txnHistory, t).txnId = t
  BY <1>1, ChooseCommit
<1>. QED
  BY <1>2, <1>3 DEF Inv, H1inv

LEMMA InvH2 ==
  ASSUME Inv
  PROVE  H2(txnHistory)
<1> SUFFICES ASSUME NEW t \in SI!CommittedTxns(txnHistory),
                    SI!KeysWrittenByTxn(txnHistory, t) # {}
             PROVE  SI!KeysReadByTxn(txnHistory, t) \subseteq SI!KeysWrittenByTxn(txnHistory, t)
  BY DEF H2
<1>1. HasBody(txnHistory, t)
  BY InvCommittedOK DEF CommittedOK
<1>2. PICK d \in Range(txnHistory) : d.type = "body" /\ d.txnId = t
  BY <1>1 DEF HasBody
<1>3. UniqueBody(txnHistory)
  BY UniqueOpsRangeBody
<1>4. BodyH2(d)
  BY <1>2 DEF Inv, H2inv
<1>5. d.reads \subseteq Keys
  BY <1>2 DEF Inv, OpShape
<1>6. \A w \in d.writes : w.key \in Keys
  BY <1>2 DEF Inv, OpShape
<1>. QED
  BY <1>2, <1>3, <1>4, <1>5, <1>6, BodyH2ToKeys

LEMMA InvH3 ==
  ASSUME Inv
  PROVE  H3(txnHistory)
<1> SUFFICES ASSUME NEW t1 \in SI!CommittedTxns(txnHistory),
                    NEW t2 \in SI!CommittedTxns(txnHistory),
                    t1 # t2,
                    SI!KeysWrittenByTxn(txnHistory, t1) \cap SI!KeysWrittenByTxn(txnHistory, t2) # {}
             PROVE  SI!CommitOp(txnHistory, t1).time < SI!BeginOp(txnHistory, t2).time
                    \/ SI!CommitOp(txnHistory, t2).time < SI!BeginOp(txnHistory, t1).time
  BY DEF H3
<1>1. HasBegin(txnHistory, t1) /\ HasCommit(txnHistory, t1)
      /\ HasBegin(txnHistory, t2) /\ HasCommit(txnHistory, t2)
  BY InvCommittedOK DEF CommittedOK
<1>2. SI!BeginOp(txnHistory, t1) \in Range(txnHistory)
      /\ SI!BeginOp(txnHistory, t1).type = "begin"
      /\ SI!BeginOp(txnHistory, t1).txnId = t1
  BY <1>1, ChooseBegin
<1>3. SI!BeginOp(txnHistory, t2) \in Range(txnHistory)
      /\ SI!BeginOp(txnHistory, t2).type = "begin"
      /\ SI!BeginOp(txnHistory, t2).txnId = t2
  BY <1>1, ChooseBegin
<1>4. SI!CommitOp(txnHistory, t1) \in Range(txnHistory)
      /\ SI!CommitOp(txnHistory, t1).type = "commit"
      /\ SI!CommitOp(txnHistory, t1).txnId = t1
  BY <1>1, ChooseCommit
<1>5. SI!CommitOp(txnHistory, t2) \in Range(txnHistory)
      /\ SI!CommitOp(txnHistory, t2).type = "commit"
      /\ SI!CommitOp(txnHistory, t2).txnId = t2
  BY <1>1, ChooseCommit
<1>. QED
  BY <1>2, <1>3, <1>4, <1>5 DEF Inv, H3inv

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
(* 8.  Initial state                                                         *)
(*****************************************************************************)

LEMMA InitInv == Init => Inv
<1> SUFFICES ASSUME Init PROVE Inv
  OBVIOUS
<1>1. txnHistory = <<>>
  BY DEF Init
<1>2. Range(txnHistory) = {}
  BY <1>1, EmptyRange
<1>3. HistSeq
  BY <1>1, EmptySeq DEF HistSeq
<1>4. ClockType
  BY DEF Init, ClockType
<1>5. OpShape
  BY <1>2 DEF OpShape
<1>6. UniqueOps
  BY <1>1, EmptySeq, LenProperties DEF UniqueOps
<1>7. TimesMono
  BY <1>1, EmptySeq, LenProperties DEF TimesMono
<1>8. TimesVsClock
  BY <1>2 DEF TimesVsClock
<1>9. OrderOK
  BY <1>1, EmptySeq, LenProperties DEF OrderOK
<1>10. CommitHasPreds
  BY <1>2 DEF CommitHasPreds
<1>11. AbortHasPreds
  BY <1>2 DEF AbortHasPreds
<1>12. H1inv
  BY <1>2 DEF H1inv
<1>13. H2inv
  BY <1>2 DEF H2inv
<1>14. H3inv
  BY <1>2 DEF H3inv
<1>15. CommitKeys
  BY <1>2 DEF CommitKeys
<1>16. RunningOK
  BY DEF Init, RunningOK
<1>. QED
  BY <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16
  DEF Inv

-----------------------------------------------------------------------------
(*****************************************************************************)
(* 9.  Stuttering                                                            *)
(*****************************************************************************)

LEMMA UnchangedInv ==
  ASSUME Inv, UNCHANGED vars
  PROVE  Inv'
BY DEF Inv, vars, HistSeq, ClockType, OpShape, UniqueOps, TimesMono, TimesVsClock,
       OrderOK, CommitHasPreds, AbortHasPreds, H1inv, H2inv, H3inv, CommitKeys, RunningOK

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
<1>7. clock' \in Nat
  BY <1>1, <1>6
<1>8. HistSeq'
  BY <1>3 DEF HistSeq
<1>9. ClockType'
  BY <1>7 DEF ClockType
<1>10. OpShape'
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
                           /\ op.reads \subseteq Keys
                           /\ \A w \in op.writes : "key" \in DOMAIN w /\ w.key \in Keys
                      /\ op.type = "commit" => "updatedKeys" \in DOMAIN op
    BY DEF OpShape
  <2>1. CASE op \in Range(txnHistory)
    BY <2>1 DEF Inv, OpShape
  <2>2. CASE op = abortOp
    <3>1. abortOp = [type |-> "abort", txnId |-> tid, time |-> clock + 1]
      BY <1>1
    <3>2. clock + 1 \in Nat
      BY <1>6
    <3>. QED
      BY <1>5, <1>6, <2>2, <3>1, <3>2
  <2>. QED
    BY <1>4, <2>1, <2>2
<1>11. UniqueOps'
  <2> SUFFICES ASSUME NEW i \in DOMAIN txnHistory', NEW j \in DOMAIN txnHistory',
                      txnHistory'[i].type = txnHistory'[j].type,
                      txnHistory'[i].txnId = txnHistory'[j].txnId
               PROVE  i = j
    BY DEF UniqueOps
  <2>1. DOMAIN txnHistory' = 1..(Len(txnHistory)+1)
    BY <1>1, <1>2, <1>3, AppendProperties, LenProperties
  <2>2. DOMAIN txnHistory = 1..Len(txnHistory)
    BY <1>2, LenProperties
  <2>3. Len(txnHistory) \in Nat
    BY <1>2, LenProperties
  <2>4. CASE i \in DOMAIN txnHistory /\ j \in DOMAIN txnHistory
    <3>1. txnHistory'[i] = txnHistory[i] /\ txnHistory'[j] = txnHistory[j]
      BY <1>1, <1>2, <2>4, AppendProperties
    <3>. QED
      BY <2>4, <3>1 DEF Inv, UniqueOps
  <2>5. CASE i = Len(txnHistory)+1 /\ j \in DOMAIN txnHistory
    <3>1. txnHistory'[i] = abortOp
      BY <1>1, <1>2, <2>1, <2>5, AppendProperties
    <3>2. txnHistory'[j] = txnHistory[j]
      BY <1>1, <1>2, <2>5, AppendProperties
    <3>3. txnHistory[j].type = "abort" /\ txnHistory[j].txnId = tid
      BY <1>5, <3>1, <3>2
    <3>4. tid \in SI!RunningTxnIds
      BY DEF AbortTxn, SI!AbortTxn
    <3>5. ~\E c \in Range(txnHistory) : c.type \in {"commit", "abort"} /\ c.txnId = tid
      BY <3>4 DEF Inv, RunningOK, SI!RunningTxnIds
    <3>6. txnHistory[j] \in Range(txnHistory)
      BY <2>2, <2>5 DEF Range
    <3>. QED
      BY <3>3, <3>5, <3>6
  <2>6. CASE j = Len(txnHistory)+1 /\ i \in DOMAIN txnHistory
    <3>1. txnHistory'[j] = abortOp
      BY <1>1, <1>2, <2>1, <2>6, AppendProperties
    <3>2. txnHistory'[i] = txnHistory[i]
      BY <1>1, <1>2, <2>6, AppendProperties
    <3>3. txnHistory[i].type = "abort" /\ txnHistory[i].txnId = tid
      BY <1>5, <3>1, <3>2
    <3>4. tid \in SI!RunningTxnIds
      BY DEF AbortTxn, SI!AbortTxn
    <3>5. ~\E c \in Range(txnHistory) : c.type \in {"commit", "abort"} /\ c.txnId = tid
      BY <3>4 DEF Inv, RunningOK, SI!RunningTxnIds
    <3>6. txnHistory[i] \in Range(txnHistory)
      BY <2>2, <2>6 DEF Range
    <3>. QED
      BY <3>3, <3>5, <3>6
  <2>. QED
    BY <2>1, <2>2, <2>4, <2>5, <2>6
<1>12. TimesMono'
  <2> SUFFICES ASSUME NEW i \in DOMAIN txnHistory', NEW j \in DOMAIN txnHistory',
                      i < j,
                      txnHistory'[i].type \in {"begin", "commit", "abort"},
                      txnHistory'[j].type \in {"begin", "commit", "abort"}
               PROVE  txnHistory'[i].time < txnHistory'[j].time
    BY DEF TimesMono
  <2>1. DOMAIN txnHistory = 1..Len(txnHistory)
    BY <1>2, LenProperties
  <2>2. CASE j \in DOMAIN txnHistory
    <3>1. i \in DOMAIN txnHistory
      BY <1>1, <1>2, <2>2, AppendProperties, LenProperties
    <3>2. txnHistory'[i] = txnHistory[i] /\ txnHistory'[j] = txnHistory[j]
      BY <1>1, <1>2, <3>1, <2>2, AppendProperties
    <3>. QED
      BY <3>1, <2>2, <3>2 DEF Inv, TimesMono
  <2>3. CASE j = Len(txnHistory)+1
    <3>1. txnHistory'[j] = abortOp
      BY <1>1, <1>2, <2>3, AppendProperties, LenProperties
    <3>2. i \in DOMAIN txnHistory
      BY <2>3, <1>2, LenProperties
    <3>3. txnHistory'[i] = txnHistory[i]
      BY <1>1, <1>2, <3>2, AppendProperties
    <3>4. txnHistory[i].type \in {"begin", "commit", "abort"}
      BY <3>3
    <3>5. txnHistory[i] \in Range(txnHistory)
      BY <3>2 DEF Range
    <3>6. txnHistory[i].time <= clock
      BY <3>3, <3>4, <3>5 DEF Inv, TimesVsClock, OpShape
    <3>7. abortOp.time = clock + 1
      BY <1>5
    <3>8. txnHistory[i].time \in Nat
      BY <3>3, <3>5 DEF Inv, OpShape
    <3>. QED
      BY <3>1, <3>3, <3>6, <3>7, <3>8, <1>6
  <2>. QED
    BY <1>1, <1>2, <2>2, <2>3, AppendProperties, LenProperties
<1>13. TimesVsClock'
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
<1>14. OrderOK'
  <2>1. \A i, j \in DOMAIN txnHistory' :
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
      BY <1>1, <1>2, <3>1, AppendProperties DEF Inv, OrderOK
    <3>2. CASE j = Len(txnHistory)+1
      <4>1. i \in DOMAIN txnHistory
        BY <1>1, <1>2, <3>2, AppendProperties, LenProperties
      <4>2. i < Len(txnHistory) + 1
        BY <1>2, <4>1, SeqIndexLtLenP1
      <4>3. j = Len(txnHistory) + 1
        BY <3>2
      <4>. QED
        BY <4>2, <4>3
    <3>3. CASE i = Len(txnHistory)+1
      <4>1. txnHistory'[i] = abortOp
        BY <1>1, <1>2, <3>3, AppendProperties, LenProperties
      <4>2. abortOp.type # "begin"
        BY <1>5
      <4>. QED
        BY <4>1, <4>2
    <3>. QED
      BY <1>1, <1>2, <3>1, <3>2, <3>3, AppendProperties, LenProperties
  <2>2. \A i, j \in DOMAIN txnHistory' :
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
      BY <1>1, <1>2, <3>1, AppendProperties DEF Inv, OrderOK
    <3>2. CASE j = Len(txnHistory)+1
      <4>1. i \in DOMAIN txnHistory
        BY <1>1, <1>2, <3>2, AppendProperties, LenProperties
      <4>2. i < Len(txnHistory) + 1
        BY <1>2, <4>1, SeqIndexLtLenP1
      <4>3. j = Len(txnHistory) + 1
        BY <3>2
      <4>. QED
        BY <4>2, <4>3
    <3>3. CASE i = Len(txnHistory)+1
      <4>1. txnHistory'[i] = abortOp
        BY <1>1, <1>2, <3>3, AppendProperties, LenProperties
      <4>2. abortOp.type # "body"
        BY <1>5
      <4>. QED
        BY <4>1, <4>2
    <3>. QED
      BY <1>1, <1>2, <3>1, <3>2, <3>3, AppendProperties, LenProperties
  <2>. QED
    BY <2>1, <2>2 DEF OrderOK
<1>15. CommitHasPreds'
  <2> SUFFICES ASSUME NEW c \in Range(txnHistory'), c.type = "commit"
               PROVE  /\ \E b \in Range(txnHistory') : b.type = "begin" /\ b.txnId = c.txnId
                      /\ \E d \in Range(txnHistory') : d.type = "body"  /\ d.txnId = c.txnId
    BY DEF CommitHasPreds
  <2>1. c \in Range(txnHistory)
    BY <1>4, <1>5
  <2>2. \E b \in Range(txnHistory) : b.type = "begin" /\ b.txnId = c.txnId
        /\ \E d \in Range(txnHistory) : d.type = "body" /\ d.txnId = c.txnId
    BY <2>1 DEF Inv, CommitHasPreds
  <2>. QED
    BY <1>4, <2>2
<1>16. AbortHasPreds'
  <2> SUFFICES ASSUME NEW a \in Range(txnHistory'), a.type = "abort"
               PROVE  /\ \E b \in Range(txnHistory') : b.type = "begin" /\ b.txnId = a.txnId
                      /\ \E d \in Range(txnHistory') : d.type = "body"  /\ d.txnId = a.txnId
    BY DEF AbortHasPreds
  <2>1. CASE a \in Range(txnHistory)
    BY <1>4, <2>1 DEF Inv, AbortHasPreds
  <2>2. CASE a = abortOp
    <3>1. tid \in SI!RunningTxnIds
      BY DEF AbortTxn, SI!AbortTxn
    <3>2. PICK txn \in runningTxns : txn.id = tid
      BY <3>1 DEF SI!RunningTxnIds
    <3>3. \E b \in Range(txnHistory) : b.type = "begin" /\ b.txnId = tid
          /\ \E d \in Range(txnHistory) : d.type = "body" /\ d.txnId = tid
      BY <3>2 DEF Inv, RunningOK
    <3>. QED
      BY <1>4, <1>5, <2>2, <3>3
  <2>. QED
    BY <1>4, <2>1, <2>2
<1>17. H1inv'
  <2> SUFFICES ASSUME NEW b \in Range(txnHistory'), NEW c \in Range(txnHistory'),
                      b.type = "begin", c.type = "commit", b.txnId = c.txnId
               PROVE  b.time < c.time
    BY DEF H1inv
  <2>1. b \in Range(txnHistory) /\ c \in Range(txnHistory)
    BY <1>4, <1>5
  <2>. QED
    BY <2>1 DEF Inv, H1inv
<1>18. H2inv'
  <2> SUFFICES ASSUME NEW d \in Range(txnHistory'), d.type = "body"
               PROVE  BodyH2(d)
    BY DEF H2inv
  <2>1. d \in Range(txnHistory)
    BY <1>4, <1>5
  <2>. QED
    BY <2>1 DEF Inv, H2inv
<1>19. H3inv'
  <2> SUFFICES ASSUME NEW c1 \in Range(txnHistory'), NEW c2 \in Range(txnHistory'),
                      c1.type = "commit", c2.type = "commit", c1.txnId # c2.txnId,
                      SI!KeysWrittenByTxn(txnHistory', c1.txnId) \cap SI!KeysWrittenByTxn(txnHistory', c2.txnId) # {}
               PROVE  \A b1, b2 \in Range(txnHistory') :
                        b1.type = "begin" /\ b1.txnId = c1.txnId /\
                        b2.type = "begin" /\ b2.txnId = c2.txnId
                        => c1.time < b2.time \/ c2.time < b1.time
    BY DEF H3inv
  <2>1. c1 \in Range(txnHistory) /\ c2 \in Range(txnHistory)
    BY <1>4, <1>5
  <2>2. SI!KeysWrittenByTxn(txnHistory', c1.txnId) = SI!KeysWrittenByTxn(txnHistory, c1.txnId)
        /\ SI!KeysWrittenByTxn(txnHistory', c2.txnId) = SI!KeysWrittenByTxn(txnHistory, c2.txnId)
    BY <1>1, <1>2, <1>5, KeysWrittenUnchangedNonBody
  <2>3. \A b1, b2 \in Range(txnHistory) :
           b1.type = "begin" /\ b1.txnId = c1.txnId /\
           b2.type = "begin" /\ b2.txnId = c2.txnId
           => c1.time < b2.time \/ c2.time < b1.time
    BY <2>1, <2>2 DEF Inv, H3inv
  <2>. QED
    BY <1>4, <1>5, <2>3
<1>20. CommitKeys'
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
<1>21. RunningOK'
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
  BY <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, <1>19, <1>20, <1>21
  DEF Inv

-----------------------------------------------------------------------------
(*****************************************************************************)
(* 11. CommitTxn                                                             *)
(*****************************************************************************)

LEMMA TimesInjective ==
  ASSUME Inv
  PROVE  \A op1, op2 \in Range(txnHistory) :
           op1.type \in {"begin", "commit", "abort"} /\
           op2.type \in {"begin", "commit", "abort"} /\
           op1.time = op2.time => op1 = op2
<1> SUFFICES ASSUME NEW op1 \in Range(txnHistory), NEW op2 \in Range(txnHistory),
                    op1.type \in {"begin", "commit", "abort"},
                    op2.type \in {"begin", "commit", "abort"},
                    op1.time = op2.time
             PROVE  op1 = op2
  OBVIOUS
<1>1. PICK i \in DOMAIN txnHistory : txnHistory[i] = op1
  BY DEF Range
<1>2. PICK j \in DOMAIN txnHistory : txnHistory[j] = op2
  BY DEF Range
<1>3. PICK S : txnHistory \in Seq(S)
  BY DEF Inv, HistSeq
<1>4. DOMAIN txnHistory = 1..Len(txnHistory)
  BY <1>3, LenProperties
<1>5. CASE i < j
  <2>1. op1.time < op2.time
    BY <1>1, <1>2, <1>5 DEF Inv, TimesMono
  <2>. QED
    BY <2>1
<1>6. CASE j < i
  <2>1. op2.time < op1.time
    BY <1>1, <1>2, <1>6 DEF Inv, TimesMono
  <2>. QED
    BY <2>1
<1>7. CASE i = j
  BY <1>1, <1>2, <1>7
<1>. QED
  BY <1>4, <1>5, <1>6, <1>7

LEMMA RunningHasBeginBody ==
  ASSUME Inv, NEW tid \in TxnIds, tid \in SI!RunningTxnIds
  PROVE  /\ \E txn \in runningTxns : txn.id = tid /\ txn.startTime \in Nat
         /\ \E b \in Range(txnHistory) : b.type = "begin" /\ b.txnId = tid
         /\ \E d \in Range(txnHistory) : d.type = "body" /\ d.txnId = tid
         /\ ~\E c \in Range(txnHistory) : c.type \in {"commit", "abort"} /\ c.txnId = tid
<1>1. PICK txn \in runningTxns : txn.id = tid
  BY DEF SI!RunningTxnIds
<1>2. txn.startTime \in Nat
  BY <1>1 DEF Inv, RunningOK
<1>. QED
  BY <1>1, <1>2 DEF Inv, RunningOK

LEMMA CommitInv ==
  ASSUME Inv, NEW tid \in TxnIds, CommitTxn(tid)
  PROVE  Inv'
<1> DEFINE commitOp == [type |-> "commit", txnId |-> tid, time |-> clock + 1,
                        updatedKeys |-> SI!KeysWrittenByTxn(txnHistory, tid)]
<1>1. /\ tid \in SI!RunningTxnIds
      /\ SI!TxnCanCommit(tid)
      /\ txnHistory' = Append(txnHistory, commitOp)
      /\ runningTxns' = {r \in runningTxns : r.id # tid}
      /\ clock' = clock + 1
      /\ UNCHANGED txnReq
  BY DEF CommitTxn, SI!CommitTxn, SI!KeysWrittenByTxn
<1>2. PICK S : txnHistory \in Seq(S)
  BY DEF Inv, HistSeq
<1>3. txnHistory' \in Seq(S \cup {commitOp})
  BY <1>1, <1>2, HistSeqAppend
<1>4. Range(txnHistory') = Range(txnHistory) \cup {commitOp}
  BY <1>1, <1>2, RangeAppend
<1>5. commitOp.type = "commit" /\ commitOp.txnId = tid /\ commitOp.time = clock + 1
      /\ commitOp.updatedKeys = SI!KeysWrittenByTxn(txnHistory, tid)
  OBVIOUS
<1>6. clock \in Nat
  BY DEF Inv, ClockType
<1>7. PICK rtxn \in runningTxns : rtxn.id = tid /\ rtxn.startTime \in Nat
                     /\ \E b \in Range(txnHistory) : b.type = "begin" /\ b.txnId = tid /\ b.time = rtxn.startTime
                     /\ \E d \in Range(txnHistory) : d.type = "body" /\ d.txnId = tid
                     /\ ~\E c \in Range(txnHistory) : c.type \in {"commit", "abort"} /\ c.txnId = tid
  BY <1>1, RunningHasBeginBody DEF Inv, RunningOK
<1>8. HistSeq'
  BY <1>3 DEF HistSeq
<1>9. ClockType'
  BY <1>1, <1>6 DEF ClockType
<1>10. OpShape'
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
                           /\ op.reads \subseteq Keys
                           /\ \A w \in op.writes : "key" \in DOMAIN w /\ w.key \in Keys
                      /\ op.type = "commit" => "updatedKeys" \in DOMAIN op
    BY DEF OpShape
  <2>1. CASE op \in Range(txnHistory)
    BY <2>1 DEF Inv, OpShape
  <2>2. CASE op = commitOp
    BY <1>5, <1>6, <2>2
  <2>. QED
    BY <1>4, <2>1, <2>2
<1>11. UniqueOps'
  <2> SUFFICES ASSUME NEW i \in DOMAIN txnHistory', NEW j \in DOMAIN txnHistory',
                      txnHistory'[i].type = txnHistory'[j].type,
                      txnHistory'[i].txnId = txnHistory'[j].txnId
               PROVE  i = j
    BY DEF UniqueOps
  <2>1. DOMAIN txnHistory' = 1..(Len(txnHistory)+1)
    BY <1>1, <1>2, <1>3, AppendProperties, LenProperties
  <2>2. DOMAIN txnHistory = 1..Len(txnHistory)
    BY <1>2, LenProperties
  <2>3. CASE i \in DOMAIN txnHistory /\ j \in DOMAIN txnHistory
    <3>1. txnHistory'[i] = txnHistory[i] /\ txnHistory'[j] = txnHistory[j]
      BY <1>1, <1>2, <2>3, AppendProperties
    <3>. QED
      BY <2>3, <3>1 DEF Inv, UniqueOps
  <2>4. CASE i = Len(txnHistory)+1 /\ j \in DOMAIN txnHistory
    <3>1. txnHistory'[i] = commitOp
      BY <1>1, <1>2, <2>1, <2>4, AppendProperties
    <3>2. txnHistory'[j] = txnHistory[j]
      BY <1>1, <1>2, <2>4, AppendProperties
    <3>3. txnHistory[j].type = "commit" /\ txnHistory[j].txnId = tid
      BY <1>5, <3>1, <3>2
    <3>4. txnHistory[j] \in Range(txnHistory)
      BY <2>2, <2>4 DEF Range
    <3>. QED
      BY <1>7, <3>3, <3>4
  <2>5. CASE j = Len(txnHistory)+1 /\ i \in DOMAIN txnHistory
    <3>1. txnHistory'[j] = commitOp
      BY <1>1, <1>2, <2>1, <2>5, AppendProperties
    <3>2. txnHistory'[i] = txnHistory[i]
      BY <1>1, <1>2, <2>5, AppendProperties
    <3>3. txnHistory[i].type = "commit" /\ txnHistory[i].txnId = tid
      BY <1>5, <3>1, <3>2
    <3>4. txnHistory[i] \in Range(txnHistory)
      BY <2>2, <2>5 DEF Range
    <3>. QED
      BY <1>7, <3>3, <3>4
  <2>. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5
<1>12. TimesMono'
  <2> SUFFICES ASSUME NEW i \in DOMAIN txnHistory', NEW j \in DOMAIN txnHistory',
                      i < j,
                      txnHistory'[i].type \in {"begin", "commit", "abort"},
                      txnHistory'[j].type \in {"begin", "commit", "abort"}
               PROVE  txnHistory'[i].time < txnHistory'[j].time
    BY DEF TimesMono
  <2>1. CASE j \in DOMAIN txnHistory
    <3>1. i \in DOMAIN txnHistory
      BY <1>1, <1>2, <2>1, AppendProperties, LenProperties
    <3>2. txnHistory'[i] = txnHistory[i] /\ txnHistory'[j] = txnHistory[j]
      BY <1>1, <1>2, <3>1, <2>1, AppendProperties
    <3>. QED
      BY <3>1, <2>1, <3>2 DEF Inv, TimesMono
  <2>2. CASE j = Len(txnHistory)+1
    <3>1. txnHistory'[j] = commitOp
      BY <1>1, <1>2, <2>2, AppendProperties, LenProperties
    <3>2. i \in DOMAIN txnHistory
      BY <2>2, <1>2, LenProperties
    <3>3. txnHistory'[i] = txnHistory[i]
      BY <1>1, <1>2, <3>2, AppendProperties
    <3>4. txnHistory[i].type \in {"begin", "commit", "abort"}
      BY <3>3
    <3>5. txnHistory[i] \in Range(txnHistory)
      BY <3>2 DEF Range
    <3>6. txnHistory[i].time <= clock
      BY <3>4, <3>5 DEF Inv, TimesVsClock, OpShape
    <3>7. txnHistory[i].time \in Nat
      BY <3>4, <3>5 DEF Inv, OpShape
    <3>. QED
      BY <3>1, <3>3, <3>6, <3>7, <1>5, <1>6
  <2>. QED
    BY <1>1, <1>2, <2>1, <2>2, AppendProperties, LenProperties
<1>13. TimesVsClock'
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
<1>14. OrderOK'
  <2>1. \A i, j \in DOMAIN txnHistory' :
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
      BY <1>1, <1>2, <3>1, AppendProperties DEF Inv, OrderOK
    <3>2. CASE j = Len(txnHistory)+1
      <4>1. i \in DOMAIN txnHistory
        BY <1>1, <1>2, <3>2, AppendProperties, LenProperties
      <4>2. i < Len(txnHistory) + 1
        BY <1>2, <4>1, SeqIndexLtLenP1
      <4>3. j = Len(txnHistory) + 1
        BY <3>2
      <4>. QED
        BY <4>2, <4>3
    <3>3. CASE i = Len(txnHistory)+1
      <4>1. txnHistory'[i] = commitOp
        BY <1>1, <1>2, <3>3, AppendProperties, LenProperties
      <4>. QED
        BY <1>5, <4>1
    <3>. QED
      BY <1>1, <1>2, <3>1, <3>2, <3>3, AppendProperties, LenProperties
  <2>2. \A i, j \in DOMAIN txnHistory' :
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
      BY <1>1, <1>2, <3>1, AppendProperties DEF Inv, OrderOK
    <3>2. CASE j = Len(txnHistory)+1
      <4>1. i \in DOMAIN txnHistory
        BY <1>1, <1>2, <3>2, AppendProperties, LenProperties
      <4>2. i < Len(txnHistory) + 1
        BY <1>2, <4>1, SeqIndexLtLenP1
      <4>3. j = Len(txnHistory) + 1
        BY <3>2
      <4>. QED
        BY <4>2, <4>3
    <3>3. CASE i = Len(txnHistory)+1
      <4>1. txnHistory'[i] = commitOp
        BY <1>1, <1>2, <3>3, AppendProperties, LenProperties
      <4>. QED
        BY <1>5, <4>1
    <3>. QED
      BY <1>1, <1>2, <3>1, <3>2, <3>3, AppendProperties, LenProperties
  <2>. QED
    BY <2>1, <2>2 DEF OrderOK
<1>15. CommitHasPreds'
  <2> SUFFICES ASSUME NEW c \in Range(txnHistory'), c.type = "commit"
               PROVE  /\ \E b \in Range(txnHistory') : b.type = "begin" /\ b.txnId = c.txnId
                      /\ \E d \in Range(txnHistory') : d.type = "body"  /\ d.txnId = c.txnId
    BY DEF CommitHasPreds
  <2>1. CASE c \in Range(txnHistory)
    BY <1>4, <2>1 DEF Inv, CommitHasPreds
  <2>2. CASE c = commitOp
    BY <1>4, <1>5, <1>7, <2>2
  <2>. QED
    BY <1>4, <2>1, <2>2
<1>16. AbortHasPreds'
  <2> SUFFICES ASSUME NEW a \in Range(txnHistory'), a.type = "abort"
               PROVE  /\ \E b \in Range(txnHistory') : b.type = "begin" /\ b.txnId = a.txnId
                      /\ \E d \in Range(txnHistory') : d.type = "body"  /\ d.txnId = a.txnId
    BY DEF AbortHasPreds
  <2>1. a \in Range(txnHistory)
    BY <1>4, <1>5
  <2>. QED
    BY <1>4, <2>1 DEF Inv, AbortHasPreds
<1>17. H1inv'
  <2> SUFFICES ASSUME NEW b \in Range(txnHistory'), NEW c \in Range(txnHistory'),
                      b.type = "begin", c.type = "commit", b.txnId = c.txnId
               PROVE  b.time < c.time
    BY DEF H1inv
  <2>1. CASE c \in Range(txnHistory)
    <3>1. b \in Range(txnHistory)
      BY <1>4, <1>5
    <3>. QED
      BY <2>1, <3>1 DEF Inv, H1inv
  <2>2. CASE c = commitOp
    <3>1. b \in Range(txnHistory)
      BY <1>4, <1>5, <2>2
    <3>2. b.txnId = tid
      BY <1>5, <2>2
    <3>3. b.time <= clock
      BY <3>1 DEF Inv, TimesVsClock, OpShape
    <3>4. b.time \in Nat
      BY <3>1 DEF Inv, OpShape
    <3>. QED
      BY <1>5, <1>6, <2>2, <3>3, <3>4
  <2>. QED
    BY <1>4, <2>1, <2>2
<1>18. H2inv'
  <2> SUFFICES ASSUME NEW d \in Range(txnHistory'), d.type = "body"
               PROVE  BodyH2(d)
    BY DEF H2inv
  <2>1. d \in Range(txnHistory)
    BY <1>4, <1>5
  <2>. QED
    BY <2>1 DEF Inv, H2inv
<1>19. H3inv'
  <2> SUFFICES ASSUME NEW c1 \in Range(txnHistory'), NEW c2 \in Range(txnHistory'),
                      c1.type = "commit", c2.type = "commit", c1.txnId # c2.txnId,
                      SI!KeysWrittenByTxn(txnHistory', c1.txnId) \cap SI!KeysWrittenByTxn(txnHistory', c2.txnId) # {}
               PROVE  \A b1, b2 \in Range(txnHistory') :
                        b1.type = "begin" /\ b1.txnId = c1.txnId /\
                        b2.type = "begin" /\ b2.txnId = c2.txnId
                        => c1.time < b2.time \/ c2.time < b1.time
    BY DEF H3inv
  <2>1. SI!KeysWrittenByTxn(txnHistory', c1.txnId) = SI!KeysWrittenByTxn(txnHistory, c1.txnId)
        /\ SI!KeysWrittenByTxn(txnHistory', c2.txnId) = SI!KeysWrittenByTxn(txnHistory, c2.txnId)
    BY <1>1, <1>2, <1>5, KeysWrittenUnchangedNonBody
  <2>2. CASE c1 \in Range(txnHistory) /\ c2 \in Range(txnHistory)
    <3>1. \A b1, b2 \in Range(txnHistory) :
             b1.type = "begin" /\ b1.txnId = c1.txnId /\
             b2.type = "begin" /\ b2.txnId = c2.txnId
             => c1.time < b2.time \/ c2.time < b1.time
      BY <2>1, <2>2 DEF Inv, H3inv
    <3> SUFFICES ASSUME NEW b1 \in Range(txnHistory'), NEW b2 \in Range(txnHistory'),
                        b1.type = "begin", b1.txnId = c1.txnId,
                        b2.type = "begin", b2.txnId = c2.txnId
                 PROVE  c1.time < b2.time \/ c2.time < b1.time
      OBVIOUS
    <3>2. b1 \in Range(txnHistory) /\ b2 \in Range(txnHistory)
      BY <1>4, <1>5
    <3>. QED
      BY <3>1, <3>2
  <2>3. CASE c1 = commitOp
    <3> SUFFICES ASSUME NEW b1 \in Range(txnHistory'), NEW b2 \in Range(txnHistory'),
                        b1.type = "begin", b1.txnId = c1.txnId,
                        b2.type = "begin", b2.txnId = c2.txnId
                 PROVE  c1.time < b2.time \/ c2.time < b1.time
      OBVIOUS
    <3>1. c2 \in Range(txnHistory)
      BY <1>4, <1>5, <2>3
    <3>2. b1 \in Range(txnHistory) /\ b2 \in Range(txnHistory)
      BY <1>4, <1>5
    <3>3. b1.txnId = tid
      BY <1>5, <2>3
    <3>4. PICK btid \in Range(txnHistory) : btid.type = "begin" /\ btid.txnId = tid /\ btid.time = rtxn.startTime
      BY <1>7
    <3>5. b1 = btid
      BY <3>2, <3>3, <3>4, UniqueOpsRangeBegin DEF UniqueBegin
    <3>6. SI!KeysWrittenByTxn(txnHistory, tid) \cap SI!KeysWrittenByTxn(txnHistory, c2.txnId) # {}
      BY <1>5, <2>1, <2>3
    <3>7. c2.updatedKeys = SI!KeysWrittenByTxn(txnHistory, c2.txnId)
      BY <3>1 DEF Inv, CommitKeys
    <3>8. SI!KeysWrittenByTxn(txnHistory, tid) \cap c2.updatedKeys # {}
      BY <3>6, <3>7
    <3>9. PICK txn \in runningTxns :
            txn.id = tid /\
            ~\E op \in SI!Range(txnHistory) :
               op.type = "commit" /\ op.time > txn.startTime /\
               SI!KeysWrittenByTxn(txnHistory, tid) \cap op.updatedKeys /= {}
      BY <1>1 DEF SI!TxnCanCommit
    <3>10. txn = rtxn
      BY <1>7, <3>9 DEF Inv, RunningOK
    <3>11. ~ (c2.time > rtxn.startTime)
      BY <3>1, <3>8, <3>9, <3>10, RangeEq DEF Inv, OpShape
    <3>12. c2.time \in Nat /\ rtxn.startTime \in Nat
      BY <3>1, <1>7 DEF Inv, OpShape
    <3>13. c2.time <= rtxn.startTime
      BY <3>11, <3>12
    <3>14. c2 # btid
      BY <3>1, <3>4 DEF Inv, OpShape
    <3>15. c2.time # btid.time
      BY <3>1, <3>4, <3>14, TimesInjective
    <3>16. c2.time < rtxn.startTime
      BY <3>4, <3>13, <3>15
    <3>17. c2.time < b1.time
      BY <3>4, <3>5, <3>16
    <3>. QED
      BY <3>17
  <2>4. CASE c2 = commitOp
    <3> SUFFICES ASSUME NEW b1 \in Range(txnHistory'), NEW b2 \in Range(txnHistory'),
                        b1.type = "begin", b1.txnId = c1.txnId,
                        b2.type = "begin", b2.txnId = c2.txnId
                 PROVE  c1.time < b2.time \/ c2.time < b1.time
      OBVIOUS
    <3>1. c1 \in Range(txnHistory)
      BY <1>4, <1>5, <2>4
    <3>2. b1 \in Range(txnHistory) /\ b2 \in Range(txnHistory)
      BY <1>4, <1>5
    <3>3. b2.txnId = tid
      BY <1>5, <2>4
    <3>4. PICK btid \in Range(txnHistory) : btid.type = "begin" /\ btid.txnId = tid /\ btid.time = rtxn.startTime
      BY <1>7
    <3>5. b2 = btid
      BY <3>2, <3>3, <3>4, UniqueOpsRangeBegin DEF UniqueBegin
    <3>6. SI!KeysWrittenByTxn(txnHistory, c1.txnId) \cap SI!KeysWrittenByTxn(txnHistory, tid) # {}
      BY <1>5, <2>1, <2>4
    <3>7. c1.updatedKeys = SI!KeysWrittenByTxn(txnHistory, c1.txnId)
      BY <3>1 DEF Inv, CommitKeys
    <3>8. SI!KeysWrittenByTxn(txnHistory, tid) \cap c1.updatedKeys # {}
      BY <3>6, <3>7
    <3>9. PICK txn \in runningTxns :
            txn.id = tid /\
            ~\E op \in SI!Range(txnHistory) :
               op.type = "commit" /\ op.time > txn.startTime /\
               SI!KeysWrittenByTxn(txnHistory, tid) \cap op.updatedKeys /= {}
      BY <1>1 DEF SI!TxnCanCommit
    <3>10. txn = rtxn
      BY <1>7, <3>9 DEF Inv, RunningOK
    <3>11. ~ (c1.time > rtxn.startTime)
      BY <3>1, <3>8, <3>9, <3>10, RangeEq DEF Inv, OpShape
    <3>12. c1.time \in Nat /\ rtxn.startTime \in Nat
      BY <3>1, <1>7 DEF Inv, OpShape
    <3>13. c1.time <= rtxn.startTime
      BY <3>11, <3>12
    <3>14. c1 # btid
      BY <3>1, <3>4 DEF Inv, OpShape
    <3>15. c1.time # btid.time
      BY <3>1, <3>4, <3>14, TimesInjective
    <3>16. c1.time < rtxn.startTime
      BY <3>4, <3>13, <3>15
    <3>17. c1.time < b2.time
      BY <3>4, <3>5, <3>16
    <3>. QED
      BY <3>17
  <2>. QED
    BY <1>4, <2>2, <2>3, <2>4
<1>20. CommitKeys'
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
<1>21. RunningOK'
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
  BY <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, <1>19, <1>20, <1>21
  DEF Inv

-----------------------------------------------------------------------------
(*****************************************************************************)
(* 12. StartAndRun                                                           *)
(*****************************************************************************)

LEMMA ItemKeyInKeys ==
  ASSUME NEW i \in IIds
  PROVE  ItemKey(i) \in Keys
BY DEF Keys, RowKeys

LEMMA BidKeyInKeys ==
  ASSUME NEW t \in TxnIds
  PROVE  BidKey(t) \in Keys
BY DEF Keys, RowKeys

LEMMA StoreBidIid ==
  ASSUME NEW req \in Requests, req.type = "StoreBid"
  PROVE  req.iid \in IIds
BY RobustMix DEF Requests

LEMMA ViewItemIid ==
  ASSUME NEW req \in Requests, req.type = "ViewItem"
  PROVE  req.iid \in IIds
BY RobustMix DEF Requests

LEMMA ProgramShape ==
  ASSUME NEW tid \in TxnIds, NEW req \in Requests, NEW snap
  PROVE  LET B == ProgramFor(tid, req, snap) IN
           /\ "reads" \in DOMAIN B
           /\ "writes" \in DOMAIN B
           /\ B.reads \subseteq Keys
           /\ \A w \in B.writes : "key" \in DOMAIN w /\ w.key \in Keys
<1>1. req.type = "StoreBid" \/ req.type = "ViewItem"
  BY RequestTypes
<1>2. CASE req.type = "StoreBid"
  <2>1. ProgramFor(tid, req, snap) = StoreBidProgram(tid, req, snap)
    BY <1>2, ProgramForStoreBid
  <2>2. req.iid \in IIds
    BY <1>2, StoreBidIid
  <2>3. ItemKey(req.iid) \in Keys
    BY <2>2, ItemKeyInKeys
  <2>4. BidKey(tid) \in Keys
    BY BidKeyInKeys
  <2>. QED
    BY <2>1, <2>3, <2>4 DEF StoreBidProgram
<1>3. CASE req.type = "ViewItem"
  <2>1. ProgramFor(tid, req, snap) = ViewItemProgram(req, snap)
    BY <1>3, ProgramForViewItem
  <2>2. req.iid \in IIds
    BY <1>3, ViewItemIid
  <2>3. ItemKey(req.iid) \in Keys
    BY <2>2, ItemKeyInKeys
  <2>. QED
    BY <2>1, <2>3 DEF ViewItemProgram
<1>. QED
  BY <1>1, <1>2, <1>3

LEMMA WritesUnchangedConcatOther ==
  ASSUME NEW S, NEW h \in Seq(S), NEW a, NEW b,
         a.type # "body",
         "txnId" \in DOMAIN b
  PROVE  \A t, k : t # b.txnId =>
           (SI!WritesKey(h \o <<a, b>>, t, k) <=> SI!WritesKey(h, t, k))
<1>1. Range(h \o <<a, b>>) = Range(h) \cup {a, b}
  BY RangeConcatPair
<1>2. SI!Range(h \o <<a, b>>) = SI!Range(h) \cup {a, b}
  BY <1>1, RangeEq
<1>. QED
  BY <1>1, <1>2 DEF SI!WritesKey

LEMMA KeysWrittenUnchangedConcatOther ==
  ASSUME NEW S, NEW h \in Seq(S), NEW a, NEW b,
         a.type # "body",
         "txnId" \in DOMAIN b
  PROVE  \A t : t # b.txnId =>
           SI!KeysWrittenByTxn(h \o <<a, b>>, t) = SI!KeysWrittenByTxn(h, t)
BY WritesUnchangedConcatOther DEF SI!KeysWrittenByTxn, Keys

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
<1>9. /\ "reads" \in DOMAIN body
      /\ "writes" \in DOMAIN body
      /\ body.reads \subseteq Keys
      /\ \A w \in body.writes : "key" \in DOMAIN w /\ w.key \in Keys
  BY ProgramShape
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
                           /\ op.reads \subseteq Keys
                           /\ \A w \in op.writes : "key" \in DOMAIN w /\ w.key \in Keys
                      /\ op.type = "commit" => "updatedKeys" \in DOMAIN op
    BY DEF OpShape
  <2>1. CASE op \in Range(txnHistory)
    BY <2>1 DEF Inv, OpShape
  <2>2. CASE op = beginOp
    BY <1>5, <1>6, <2>2
  <2>3. CASE op = bodyOp
    BY <1>5, <1>9, <2>3
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
      <4>0. DOMAIN txnHistory' = 1..(Len(txnHistory)+2)
        BY <1>1, <1>2, <1>3, ConcatProperties, PairSeq, SeqMonotonic, LenProperties
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
      <4>0. DOMAIN txnHistory' = 1..(Len(txnHistory)+2)
        BY <1>1, <1>2, <1>3, ConcatProperties, PairSeq, SeqMonotonic, LenProperties
      <4>1. j = Len(txnHistory)+1 \/ j = Len(txnHistory)+2
        BY <1>1, <1>2, <1>3, <3>2, NewConcatIndex
      <4>2. txnHistory'[j].type \in {"begin", "body"}
        BY <4>1, <1>5, <2>3, <2>4
      <4>. QED
        BY <4>2
    <3>3. CASE i \notin DOMAIN txnHistory /\ j \in DOMAIN txnHistory
      <4>0. DOMAIN txnHistory' = 1..(Len(txnHistory)+2)
        BY <1>1, <1>2, <1>3, ConcatProperties, PairSeq, SeqMonotonic, LenProperties
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
  <2>1. c \in Range(txnHistory)
    BY <1>4, <1>5
  <2>2. CASE b \in Range(txnHistory)
    BY <2>1, <2>2 DEF Inv, H1inv
  <2>3. CASE b = beginOp
    <3>1. c.txnId = tid
      BY <1>5, <2>3
    <3>. QED
      BY <1>7, <2>1, <3>1
  <2>. QED
    BY <1>4, <2>2, <2>3
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
    BY <1>4, <1>5, <2>1, <2>2
<1>21. H3inv'
  <2> SUFFICES ASSUME NEW c1 \in Range(txnHistory'), NEW c2 \in Range(txnHistory'),
                      c1.type = "commit", c2.type = "commit", c1.txnId # c2.txnId,
                      SI!KeysWrittenByTxn(txnHistory', c1.txnId) \cap SI!KeysWrittenByTxn(txnHistory', c2.txnId) # {}
               PROVE  \A b1, b2 \in Range(txnHistory') :
                        b1.type = "begin" /\ b1.txnId = c1.txnId /\
                        b2.type = "begin" /\ b2.txnId = c2.txnId
                        => c1.time < b2.time \/ c2.time < b1.time
    BY DEF H3inv
  <2>1. c1 \in Range(txnHistory) /\ c2 \in Range(txnHistory)
    BY <1>4, <1>5
  <2>2. c1.txnId # tid /\ c2.txnId # tid
    BY <1>7, <2>1
  <2>3. SI!KeysWrittenByTxn(txnHistory', c1.txnId) = SI!KeysWrittenByTxn(txnHistory, c1.txnId)
        /\ SI!KeysWrittenByTxn(txnHistory', c2.txnId) = SI!KeysWrittenByTxn(txnHistory, c2.txnId)
    BY <1>1, <1>2, <1>5, <2>2, KeysWrittenUnchangedConcatOther
  <2>4. \A b1, b2 \in Range(txnHistory) :
           b1.type = "begin" /\ b1.txnId = c1.txnId /\
           b2.type = "begin" /\ b2.txnId = c2.txnId
           => c1.time < b2.time \/ c2.time < b1.time
    BY <2>1, <2>3 DEF Inv, H3inv
  <2> SUFFICES ASSUME NEW b1 \in Range(txnHistory'), NEW b2 \in Range(txnHistory'),
                      b1.type = "begin", b1.txnId = c1.txnId,
                      b2.type = "begin", b2.txnId = c2.txnId
               PROVE  c1.time < b2.time \/ c2.time < b1.time
    OBVIOUS
  <2>5. b1 \in Range(txnHistory) /\ b2 \in Range(txnHistory)
    BY <1>4, <1>5, <2>2
  <2>. QED
    BY <2>4, <2>5
<1>22. CommitKeys'
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
<1>23. RunningOK'
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
        BY <3>1 DEF Inv, RunningOK
      <4>3. ~\E c \in Range(txnHistory') : c.type \in {"commit", "abort"} /\ c.txnId = txn.id
        BY <1>4, <1>5, <4>1, <4>2
      <4>. QED
        BY <1>4, <4>2, <4>3
    <3>2. CASE txn = newTxn
      <4>1. \E b \in Range(txnHistory') : b.type = "begin" /\ b.txnId = tid /\ b.time = clock + 1
        BY <1>4, <1>5
      <4>2. \E d \in Range(txnHistory') : d.type = "body" /\ d.txnId = tid
        BY <1>4, <1>5
      <4>3. ~\E c \in Range(txnHistory') : c.type \in {"commit", "abort"} /\ c.txnId = tid
        BY <1>4, <1>5, <1>7
      <4>. QED
        BY <1>5, <3>2, <4>1, <4>2, <4>3
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
        BY <1>5, <3>2
      <4>2. CASE t2 \in runningTxns
        BY <1>7, <4>1, <4>2 DEF Inv, RunningOK
      <4>3. CASE t2 = newTxn
        BY <3>2, <4>3
      <4>. QED
        BY <1>1, <4>2, <4>3
    <3>3. CASE t2 = newTxn
      <4>1. t1.id = tid
        BY <1>5, <3>3
      <4>2. CASE t1 \in runningTxns
        BY <1>7, <4>1, <4>2 DEF Inv, RunningOK
      <4>3. CASE t1 = newTxn
        BY <3>3, <4>3
      <4>. QED
        BY <1>1, <4>2, <4>3
    <3>. QED
      BY <1>1, <3>1, <3>2, <3>3
  <2>. QED
    BY <2>2, <2>3, <2>4 DEF RunningOK
<1>. QED
  BY <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, <1>19, <1>20, <1>21, <1>22, <1>23
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
