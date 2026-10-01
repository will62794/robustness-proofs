-------------------------------- MODULE Auction_Proofs --------------------------------
EXTENDS Auction, TLAPS, NaturalsInduction, SequenceTheorems, FiniteSetTheorems

(**************************************************************************************************)
(*                                                                                                *)
(* PART 1.  A GENERIC ACYCLICITY CRITERION                                                        *)
(*                                                                                                *)
(* If every edge of a graph strictly increases some natural-valued ranking of its nodes, the      *)
(* graph has no cycle.  Nothing here is specific to the auction.                                  *)
(*                                                                                                *)
(**************************************************************************************************)

\* A path of `edges` has the length its index set says it has.  Finiteness of the node set is what
\* makes `maxLen` a natural number, which is what pins `Len(p)` down.
LEMMA PathLen ==
    ASSUME NEW edges, IsFiniteSet(GraphNodes(edges)), NEW p \in Paths(edges)
    PROVE  /\ Len(p) \in Nat
           /\ DOMAIN p = 1..Len(p)
           /\ \A i \in 1..Len(p) : p[i] \in GraphNodes(edges)
           /\ \A i \in 1..(Len(p)-1) : <<p[i], p[i+1]>> \in edges
<1> DEFINE nodes == GraphNodes(edges)
<1>a Cardinality(nodes) \in Nat
  BY FS_CardinalityType
<1>1 PICK n \in Nat : p \in [1..n -> nodes]
  <2>1 PICK m \in 1..(Cardinality(nodes) + 1) : p \in [1..m -> nodes]
    BY DEF Paths
  <2>2 m \in Nat
    BY <2>1, <1>a
  <2> QED BY <2>1, <2>2
<1>3 p \in Seq(nodes)
  BY <1>1, SeqDef
<1>4 Len(p) = n
  <2>1 /\ DOMAIN p = 1..Len(p)
       /\ Len(p) \in Nat
    BY <1>3, LenProperties
  <2>2 DOMAIN p = 1..n
    BY <1>1
  <2>3 1..Len(p) = 1..n
    BY <2>1, <2>2
  \* 1..a = 1..b with a, b naturals forces a = b: each endpoint lies in its own range, hence in
  \* the other's.  The empty case (either endpoint 0) is handled separately.
  <2>4 CASE n = 0
    BY <2>3, <2>4, <2>1
  <2>5 CASE n # 0
    <3>1 n \in 1..n /\ n \in Nat
      BY <2>5, <1>1
    <3>2 n \in 1..Len(p)
      BY <3>1, <2>3
    <3>3 n =< Len(p)
      BY <3>2, <2>1
    <3>4 Len(p) # 0
      BY <3>3, <3>1, <2>1
    <3>5 Len(p) \in 1..Len(p)
      BY <3>4, <2>1
    <3>6 Len(p) =< n
      BY <3>5, <2>3, <1>1
    <3>7 Len(p) \in Nat /\ n \in Nat
      BY <2>1, <1>1
    <3> QED BY <3>3, <3>6, <3>7
  <2> QED BY <2>4, <2>5
<1> QED BY <1>1, <1>3, <1>4, LenProperties DEF Paths

(**************************************************************************************************)
(* The ranking criterion.                                                                         *)
(**************************************************************************************************)
LEMMA RankImpliesAcyclic ==
    ASSUME NEW edges, NEW N, NEW f(_),
           IsFiniteSet(GraphNodes(edges)),
           \A e \in edges : e[1] \in N /\ e[2] \in N,
           \A x \in N : f(x) \in Nat,
           \A e \in edges : f(e[1]) < f(e[2])
    PROVE  ~IsCycleViaPath(edges)
<1> SUFFICES ASSUME NEW p \in Paths(edges), Len(p) > 1, p[1] = p[Len(p)]
             PROVE  FALSE
  BY DEF IsCycleViaPath
<1> DEFINE n == Len(p)
<1>1 /\ n \in Nat
     /\ \A i \in 1..n : p[i] \in GraphNodes(edges)
     /\ \A i \in 1..(n-1) : <<p[i], p[i+1]>> \in edges
  BY PathLen
<1>2 GraphNodes(edges) \subseteq N
  BY DEF GraphNodes
<1>3 \A i \in 1..n : f(p[i]) \in Nat
  BY <1>1, <1>2
\* Every node of the path strictly outranks the path's first node.
<1> DEFINE P(j) == (j \in 2..n) => f(p[1]) < f(p[j])
<1>4 P(0)
  OBVIOUS
<1>5 \A j \in Nat : P(j) => P(j+1)
  <2> SUFFICES ASSUME NEW j \in Nat, P(j), (j+1) \in 2..n
               PROVE  f(p[1]) < f(p[j+1])
    OBVIOUS
  <2>1 j \in 1..(n-1)
    BY <1>1
  <2>2 <<p[j], p[j+1]>> \in edges
    BY <2>1, <1>1
  <2>3 f(p[j]) < f(p[j+1])
    BY <2>2
  <2>4 CASE j = 1
    BY <2>3, <2>4
  <2>5 CASE j # 1
    <3>1 j \in 2..n
      BY <2>1, <2>5, <1>1
    <3>2 f(p[1]) < f(p[j])
      BY <3>1, P(j)
    <3>3 /\ f(p[1]) \in Nat
         /\ f(p[j]) \in Nat
         /\ f(p[j+1]) \in Nat
      BY <1>3, <1>1, <3>1
    <3> QED BY <3>2, <2>3, <3>3
  <2> QED BY <2>4, <2>5
<1>6 \A j \in Nat : P(j)
  BY <1>4, <1>5, NatInduction, Isa
<1>7 n \in 2..n
  BY <1>1
<1>8 f(p[1]) < f(p[n])
  BY <1>6, <1>7, <1>1
<1> QED BY <1>8, <1>3, <1>1, <1>7


----------------------------------------------------------------------------------------------------

(**************************************************************************************************)
(*                                                                                                *)
(* PART 2.  THE ROBUST MIX, AND THE RANKING THAT WITNESSES ITS ACYCLICITY                         *)
(*                                                                                                *)
(* `SerializableViaPath` is NOT a theorem of this module for an arbitrary `EnabledTxnTypes`:      *)
(* RegUser breaks it (Figure 2(d) of the paper, and the `auction-reguser` config, where TLC finds *)
(* the write skew).  The theorem below is about the paper's robust mix, StoreBid + ViewItem.      *)
(*                                                                                                *)
(**************************************************************************************************)

ASSUME RobustMix == EnabledTxnTypes \subseteq {"StoreBid", "ViewItem"}

(**************************************************************************************************)
(* The three facts about a history that the acyclicity argument consumes.  Only the third is      *)
(* about the workload; the first two hold for any workload under snapshot isolation.              *)
(*                                                                                                *)
(*   TimesOK   every committed transaction began before it committed.                             *)
(*   FCWOK     First-Committer-Wins: two committed transactions that write a common key have      *)
(*             disjoint lifetimes, so one committed before the other began.                       *)
(*   ShapeOK   a committed transaction that writes anything writes everything it reads.  For the  *)
(*             robust mix this is just the shape of StoreBid, whose body is the read-modify-write *)
(*             `nbids := nbids + 1` on the single item it reads; ViewItem writes nothing, so the  *)
(*             implication is vacuous for it.  This is what rules out two consecutive rw edges.   *)
(**************************************************************************************************)

Writer(h, t) == \E k \in Keys : WritesKey(h, t, k)

TimesOK(h) ==
    \A t \in CommittedTxns(h) :
        /\ BeginOp(h, t).time \in Nat
        /\ CommitOp(h, t).time \in Nat
        /\ BeginOp(h, t).time < CommitOp(h, t).time

FCWOK(h) ==
    \A t1, t2 \in CommittedTxns(h) :
        t1 # t2 =>
        \A k \in Keys :
            (WritesKey(h, t1, k) /\ WritesKey(h, t2, k)) =>
                \/ CommitOp(h, t1).time =< BeginOp(h, t2).time
                \/ CommitOp(h, t2).time =< BeginOp(h, t1).time

ShapeOK(h) ==
    \A t \in CommittedTxns(h) :
        Writer(h, t) => \A k \in Keys : ReadsKey(h, t, k) => WritesKey(h, t, k)

MVSGOK(h) == TimesOK(h) /\ FCWOK(h) /\ ShapeOK(h)

(**************************************************************************************************)
(* The ranking.  A writer is ranked by when it committed, a read-only transaction by when it      *)
(* began.  (Ranking everything by commit time does not work: a read-only transaction may begin    *)
(* before, and commit after, a writer it has an rw edge to.)                                      *)
(**************************************************************************************************)
Rank(h, t) == IF Writer(h, t) THEN CommitOp(h, t).time ELSE BeginOp(h, t).time

LEMMA RankType ==
    ASSUME NEW h, TimesOK(h), NEW t \in CommittedTxns(h)
    PROVE  Rank(h, t) \in Nat
BY DEF Rank, TimesOK

(**************************************************************************************************)
(* Every MVSG edge strictly increases the rank.                                                   *)
(**************************************************************************************************)
LEMMA EdgeIncreasesRank ==
    ASSUME NEW h, MVSGOK(h), NEW e \in SerializationGraph(h)
    PROVE  Rank(h, e[1]) < Rank(h, e[2])
<1> DEFINE t1 == e[1]
            t2 == e[2]
<1>0 /\ t1 \in CommittedTxns(h)
     /\ t2 \in CommittedTxns(h)
     /\ t1 # t2
     /\ \/ WWDependency(h, t1, t2)
        \/ WRDependency(h, t1, t2)
        \/ RWDependency(h, t1, t2)
  BY DEF SerializationGraph
<1>t /\ BeginOp(h, t1).time \in Nat /\ CommitOp(h, t1).time \in Nat
     /\ BeginOp(h, t1).time < CommitOp(h, t1).time
     /\ BeginOp(h, t2).time \in Nat /\ CommitOp(h, t2).time \in Nat
     /\ BeginOp(h, t2).time < CommitOp(h, t2).time
  BY <1>0 DEF MVSGOK, TimesOK
\* ww: both transactions write, so both are ranked by commit time, and the edge says so directly.
<1>1 CASE WWDependency(h, t1, t2)
  <2>1 Writer(h, t1) /\ Writer(h, t2)
    BY <1>1 DEF WWDependency, Writer
  <2> QED BY <2>1, <1>1 DEF Rank, WWDependency
\* wr: t1 is a writer (rank = its commit time) and the edge puts that before t2's begin, which is
\* at most t2's rank either way.
<1>2 CASE WRDependency(h, t1, t2)
  <2>1 Writer(h, t1)
    BY <1>2 DEF WRDependency, Writer
  <2>2 CommitOp(h, t1).time < BeginOp(h, t2).time
    BY <1>2 DEF WRDependency
  <2>3 BeginOp(h, t2).time =< Rank(h, t2)
    BY <1>t DEF Rank
  <2> QED BY <2>1, <2>2, <2>3, <1>t DEF Rank
\* rw: t2 is a writer, so its rank is its commit time, which the edge puts after t1's begin.
<1>3 CASE RWDependency(h, t1, t2)
  <2>1 PICK k \in Keys : ReadsKey(h, t1, k) /\ WritesKey(h, t2, k)
    BY <1>3 DEF RWDependency
  <2>2 Writer(h, t2) /\ Rank(h, t2) = CommitOp(h, t2).time
    BY <2>1 DEF Writer, Rank
  <2>3 BeginOp(h, t1).time < CommitOp(h, t2).time
    BY <1>3 DEF RWDependency
  \* If t1 reads only, its rank is its begin time and the edge gives the result at once.
  <2>4 CASE ~Writer(h, t1)
    BY <2>4, <2>2, <2>3 DEF Rank
  \* Otherwise t1 is a writer, and ShapeOK makes it write the very key k it read.  Now t1 and t2
  \* both write k, so First-Committer-Wins forces their lifetimes apart; the edge's own
  \* begin(t1) < commit(t2) rules out t2 being the earlier one.
  <2>5 CASE Writer(h, t1)
    <3>1 WritesKey(h, t1, k)
      BY <2>5, <2>1, <1>0 DEF MVSGOK, ShapeOK
    <3>2 \/ CommitOp(h, t1).time =< BeginOp(h, t2).time
         \/ CommitOp(h, t2).time =< BeginOp(h, t1).time
      BY <3>1, <2>1, <1>0 DEF MVSGOK, FCWOK
    <3>3 ~(CommitOp(h, t2).time =< BeginOp(h, t1).time)
      BY <2>3, <1>t
    <3>4 CommitOp(h, t1).time =< BeginOp(h, t2).time
      BY <3>2, <3>3
    <3>5 Rank(h, t1) = CommitOp(h, t1).time
      BY <2>5 DEF Rank
    <3> QED BY <3>4, <3>5, <2>2, <1>t
  <2> QED BY <2>4, <2>5
<1> QED BY <1>0, <1>1, <1>2, <1>3

(**************************************************************************************************)
(* Hence any history satisfying the three facts is conflict serializable.                         *)
(**************************************************************************************************)
LEMMA MVSGOKImpliesSerializable ==
    ASSUME NEW h, MVSGOK(h), IsFiniteSet(CommittedTxns(h))
    PROVE  IsConflictSerializableViaPath(h)
<1> DEFINE edges == SerializationGraph(h)
            N     == CommittedTxns(h)
            f(t)  == Rank(h, t)
<1>1 \A e \in edges : e[1] \in N /\ e[2] \in N
  BY DEF SerializationGraph
<1>2 \A x \in N : f(x) \in Nat
  BY RankType DEF MVSGOK
<1>3 \A e \in edges : f(e[1]) < f(e[2])
  BY EdgeIncreasesRank
<1>4 IsFiniteSet(GraphNodes(edges))
  <2>1 GraphNodes(edges) \subseteq N
    BY <1>1 DEF GraphNodes
  <2> QED BY <2>1, FS_Subset
<1> QED BY <1>1, <1>2, <1>3, <1>4, RankImpliesAcyclic DEF IsConflictSerializableViaPath


----------------------------------------------------------------------------------------------------

(**************************************************************************************************)
(*                                                                                                *)
(* PART 3.  AN INDUCTIVE INVARIANT ESTABLISHING `MVSGOK(txnHistory)`                              *)
(*                                                                                                *)
(* Part 2 reduced serializability to three facts about the history.  This part shows the spec     *)
(* maintains them, which needs a handful of structural facts about `txnHistory` as well:          *)
(* each transaction contributes at most one event of each type (so `BeginOp` / `CommitOp` are     *)
(* determinate), every recorded time lies in `1..clock`, and every commit event's `updatedKeys`   *)
(* really is the set of keys its transaction wrote.                                               *)
(*                                                                                                *)
(**************************************************************************************************)

(**************************************************************************************************)
(* The history's type.                                                                            *)
(*                                                                                                *)
(* Purely STRUCTURAL: that `txnHistory` is a sequence, and nothing about the shape of its events. *)
(* Typing the events would mean typing the *values* they carry, and hence carrying a type         *)
(* invariant for `dataStore`, since StoreBid writes `snap[ItemKey(i)] + 1`.  The MVSG reads only  *)
(* keys and times, so nothing downstream needs it; the field-level facts the proof does use come  *)
(* from the other conjuncts of `Inv` (`TimesBounded`, `CommitKeys`, `BodyShape`).                 *)
(**************************************************************************************************)

\* `h = [i \in DOMAIN h |-> h[i]]` is how "h is a function" is said without a type for its values.
IsSeqStruct(h) == /\ Len(h) \in Nat
                  /\ DOMAIN h = 1..Len(h)
                  /\ h = [i \in 1..Len(h) |-> h[i]]

\* A structural sequence is a sequence over its own range, which is what lets the standard
\* `Sequences` theorems apply to it without naming an element type.
LEMMA SeqStructIsSeq ==
    ASSUME NEW h, IsSeqStruct(h), NEW S, Range(h) \subseteq S
    PROVE  h \in Seq(S)
<1>1 \A i \in 1..Len(h) : h[i] \in S
  BY DEF IsSeqStruct, Range
<1>3 h \in [1..Len(h) -> S]
  BY <1>1 DEF IsSeqStruct
<1> QED BY <1>3, SeqDef DEF IsSeqStruct

(**************************************************************************************************)
(* How appending to a history extends its range.  Stated structurally, so that they apply to      *)
(* `txnHistory` without typing its events.                                                        *)
(**************************************************************************************************)

LEMMA RangeAppend ==
    ASSUME NEW h, IsSeqStruct(h), NEW a
    PROVE  /\ IsSeqStruct(Append(h, a))
           /\ Range(Append(h, a)) = Range(h) \cup {a}
<1> DEFINE S == Range(h) \cup {a}
<1>1 h \in Seq(S)
  BY SeqStructIsSeq
<1>3 Append(h, a) \in Seq(S)
  BY <1>1, AppendProperties
<1>4 IsSeqStruct(Append(h, a))
  BY <1>3, LenProperties DEF IsSeqStruct
<1>5 Append(h, a) = h \o <<a>>
  BY <1>1, AppendIsConcat
<1>6 <<a>> \in Seq(S)
  OBVIOUS
<1>7 Range(h \o <<a>>) = Range(h) \cup Range(<<a>>)
  BY <1>1, <1>6, RangeConcatenation
<1>8 Range(<<a>>) = {a}
  BY DEF Range
<1> QED BY <1>4, <1>5, <1>7, <1>8

LEMMA RangeConcat2 ==
    ASSUME NEW h, IsSeqStruct(h), NEW a, NEW b
    PROVE  /\ IsSeqStruct(h \o <<a, b>>)
           /\ Range(h \o <<a, b>>) = Range(h) \cup {a, b}
<1> DEFINE S == Range(h) \cup {a, b}
<1>1 h \in Seq(S)
  BY SeqStructIsSeq
<1>2 <<a, b>> \in Seq(S)
  OBVIOUS
<1>3 h \o <<a, b>> \in Seq(S)
  BY <1>1, <1>2, ConcatProperties
<1>4 IsSeqStruct(h \o <<a, b>>)
  BY <1>3, LenProperties DEF IsSeqStruct
<1>5 Range(h \o <<a, b>>) = Range(h) \cup Range(<<a, b>>)
  BY <1>1, <1>2, RangeConcatenation
<1>6 Range(<<a, b>>) = {a, b}
  BY DEF Range
<1> QED BY <1>4, <1>5, <1>6


(**************************************************************************************************)
(* With at most one event of each type per transaction, `BeginOp` and `CommitOp` are determinate. *)
(**************************************************************************************************)

UniqueOps(h) ==
    \A o1, o2 \in Range(h) : (o1.txnId = o2.txnId /\ o1.type = o2.type) => o1 = o2

LEMMA BeginOpIs ==
    ASSUME NEW h, UniqueOps(h), NEW t,
           NEW op \in Range(h), op.txnId = t, op.type = "begin"
    PROVE  BeginOp(h, t) = op
<1>1 \E o \in Range(h) : o.txnId = t /\ o.type = "begin"
  OBVIOUS
<1>2 LET c == CHOOSE o \in Range(h) : o.txnId = t /\ o.type = "begin"
     IN c \in Range(h) /\ c.txnId = t /\ c.type = "begin"
  BY <1>1
<1> QED BY <1>2 DEF BeginOp, UniqueOps

LEMMA CommitOpIs ==
    ASSUME NEW h, UniqueOps(h), NEW t,
           NEW op \in Range(h), op.txnId = t, op.type = "commit"
    PROVE  CommitOp(h, t) = op
<1>1 \E o \in Range(h) : o.txnId = t /\ o.type = "commit"
  OBVIOUS
<1>2 LET c == CHOOSE o \in Range(h) : o.txnId = t /\ o.type = "commit"
     IN c \in Range(h) /\ c.txnId = t /\ c.type = "commit"
  BY <1>1
<1> QED BY <1>2 DEF CommitOp, UniqueOps

LEMMA CommittedHasCommitOp ==
    ASSUME NEW h, NEW t \in CommittedTxns(h)
    PROVE  \E op \in Range(h) : op.txnId = t /\ op.type = "commit"
BY DEF CommittedTxns


(**************************************************************************************************)
(*                                                                                                *)
(* The inductive invariant.                                                                       *)
(*                                                                                                *)
(* Each conjunct earns its place by what Part 2 (or a later conjunct) needs of it:                *)
(*                                                                                                *)
(*   HTypeOK      the history is a sequence (structurally: indices 1..Len).                       *)
(*   UniqueOps    at most one event of each type per transaction, so `BeginOp` and `CommitOp` are *)
(*                determinate.  Maintained because a transaction begins only while `Unused`, and  *)
(*                commits or aborts only while running, which it stops being at once.             *)
(*   TimesBounded every recorded time lies in `1..clock`, which is what orders events against     *)
(*                `runningTxns` start times.                                                      *)
(*   RunningOK    a running transaction has a begin event at its own `startTime`, no commit or    *)
(*                abort event, and (once it has run its body) a recorded body.                    *)
(*   CommitKeys   a commit event's `updatedKeys` is exactly the set of keys its transaction wrote. *)
(*   BeganBefore  a committed transaction's begin event precedes its commit event in time.        *)
(*   BodyShape    the body of every transaction that has one has the StoreBid-or-ViewItem shape:  *)
(*                if it writes at all, it writes every key it reads.  This is the one workload    *)
(*                fact, and the whole reason the robust mix is robust.                            *)
(*   IdsOK        every event names a transaction in `TxnIds`, which bounds the committed set and *)
(*                so makes it finite.                                                             *)
(*   FCW          two distinct committed transactions writing a common key have disjoint          *)
(*                lifetimes.  Maintained by the First-Committer-Wins guard on `CommitTxn`.        *)
(*                                                                                                *)
(**************************************************************************************************)

HTypeOK == IsSeqStruct(txnHistory)

TimesBounded ==
    \A op \in Range(txnHistory) :
        op.type \in {"begin", "commit", "abort"} => op.time \in 1..clock

\* A transaction's body event, if it has one.
HasBody(t) == \E op \in Range(txnHistory) : op.txnId = t /\ op.type = "body"

RunningOK ==
    \A r \in runningTxns :
        /\ r.startTime \in 1..clock
        /\ \E op \in Range(txnHistory) :
               op.txnId = r.id /\ op.type = "begin" /\ op.time = r.startTime
        /\ ~\E op \in Range(txnHistory) :
               op.txnId = r.id /\ op.type \in {"commit", "abort"}

CommitKeys ==
    \A op \in Range(txnHistory) :
        op.type = "commit" =>
            \A k \in Keys : k \in op.updatedKeys <=> WritesKey(txnHistory, op.txnId, k)

BeganBefore ==
    \A t \in CommittedTxns(txnHistory) :
        \E b, c \in Range(txnHistory) :
            /\ b.txnId = t /\ b.type = "begin"
            /\ c.txnId = t /\ c.type = "commit"
            /\ b.time < c.time

\* The workload fact: a body that writes writes every key it reads.
BodyShape ==
    \A op \in Range(txnHistory) :
        (op.type = "body" /\ op.writes # {}) =>
            \A k \in op.reads : \E w \in op.writes : w.key = k

IdsOK == \A op \in Range(txnHistory) : op.txnId \in TxnIds

FCW ==
    \A t1, t2 \in CommittedTxns(txnHistory) :
        t1 # t2 =>
        \A k \in Keys :
            (WritesKey(txnHistory, t1, k) /\ WritesKey(txnHistory, t2, k)) =>
                \/ CommitOp(txnHistory, t1).time =< BeginOp(txnHistory, t2).time
                \/ CommitOp(txnHistory, t2).time =< BeginOp(txnHistory, t1).time

Inv ==
    /\ clock \in Nat
    /\ HTypeOK
    /\ UniqueOps(txnHistory)
    /\ TimesBounded
    /\ RunningOK
    /\ CommitKeys
    /\ BeganBefore
    /\ BodyShape
    /\ IdsOK
    /\ FCW

(**************************************************************************************************)
(* `Inv` delivers the three facts Part 2 consumes.                                                *)
(**************************************************************************************************)

LEMMA InvImpliesMVSGOK ==
    ASSUME Inv
    PROVE  MVSGOK(txnHistory)
<1> DEFINE h == txnHistory
<1>u UniqueOps(h)
  BY DEF Inv
<1>1 TimesOK(h)
  <2> SUFFICES ASSUME NEW t \in CommittedTxns(h)
               PROVE  /\ BeginOp(h, t).time \in Nat
                      /\ CommitOp(h, t).time \in Nat
                      /\ BeginOp(h, t).time < CommitOp(h, t).time
    BY DEF TimesOK
  <2>1 PICK b, c \in Range(h) :
          /\ b.txnId = t /\ b.type = "begin"
          /\ c.txnId = t /\ c.type = "commit"
          /\ b.time < c.time
    BY DEF Inv, BeganBefore
  <2>2 BeginOp(h, t) = b /\ CommitOp(h, t) = c
    BY <2>1, <1>u, BeginOpIs, CommitOpIs
  <2>3 b.time \in 1..clock /\ c.time \in 1..clock
    BY <2>1 DEF Inv, TimesBounded
  <2> QED BY <2>1, <2>2, <2>3 DEF Inv
<1>2 FCWOK(h)
  BY DEF Inv, FCW, FCWOK
\* ShapeOK is BodyShape, transported from the body event to the `ReadsKey` / `WritesKey` view.
<1>3 ShapeOK(h)
  <2> SUFFICES ASSUME NEW t \in CommittedTxns(h), Writer(h, t),
                      NEW k \in Keys, ReadsKey(h, t, k)
               PROVE  WritesKey(h, t, k)
    BY DEF ShapeOK
  <2>1 PICK ro \in Range(h) : ro.txnId = t /\ ro.type = "body" /\ k \in ro.reads
    BY DEF ReadsKey
  <2>2 PICK j \in Keys, wo \in Range(h) :
          wo.txnId = t /\ wo.type = "body" /\ \E w \in wo.writes : w.key = j
    BY DEF Writer, WritesKey
  <2>3 wo = ro
    BY <2>1, <2>2, <1>u DEF UniqueOps
  <2>4 ro.writes # {}
    BY <2>2, <2>3
  <2>5 \E w \in ro.writes : w.key = k
    BY <2>1, <2>4 DEF Inv, BodyShape
  <2> QED BY <2>1, <2>5 DEF WritesKey
<1> QED BY <1>1, <1>2, <1>3 DEF MVSGOK

\* `Inv` minus the structural type conjunct, so that TLC can check the substantive conjuncts
\* directly (it reports `DOMAIN h = 1..Len(h)` as a comparison it cannot evaluate).
InvNoType ==
    /\ clock \in Nat
    /\ UniqueOps(txnHistory)
    /\ TimesBounded
    /\ RunningOK
    /\ CommitKeys
    /\ BeganBefore
    /\ BodyShape
    /\ IdsOK
    /\ FCW


(**************************************************************************************************)
(*                                                                                                *)
(* Workload facts.  Everything the inductive step needs to know about the programs: for the       *)
(* robust mix each body is well typed and, if it writes anything, writes every key it reads.      *)
(*                                                                                                *)
(**************************************************************************************************)

LEMMA ProgramShape ==
    ASSUME NEW tid \in TxnIds, NEW req \in Requests, NEW snap
    PROVE  LET p == ProgramFor(tid, req, snap) IN
           /\ p.reads \subseteq Keys
           /\ (p.writes # {} => \A k \in p.reads : \E w \in p.writes : w.key = k)
<1> DEFINE p == ProgramFor(tid, req, snap)
\* The robust mix admits only StoreBid and ViewItem requests.
<1>1 req.type \in {"StoreBid", "ViewItem"}
  BY RobustMix DEF Requests
\* StoreBid: reads ITEMS(iid) and writes both ITEMS(iid) and its own fresh BIDS key, so the
\* single key it reads is among the keys it writes.
<1>2 CASE req.type = "StoreBid"
  <2>1 PICK i \in IIds : req = [type |-> "StoreBid", iid |-> i]
    BY <1>2, RobustMix DEF Requests
  <2>2 p = StoreBidProgram(tid, req, snap)
    BY <1>2 DEF ProgramFor
  <2>3 p.reads = {ItemKey(i)}
    BY <2>1, <2>2 DEF StoreBidProgram
  <2>4 p.writes = {[type |-> "write", key |-> BidKey(tid), val |-> Tag],
                   [type |-> "write", key |-> ItemKey(i), val |-> snap[ItemKey(i)] + 1]}
    BY <2>1, <2>2 DEF StoreBidProgram
  <2>5 ItemKey(i) \in Keys /\ BidKey(tid) \in Keys
    BY <2>1 DEF Keys, RowKeys
  <2>6 \A k \in p.reads : \E w \in p.writes : w.key = k
    BY <2>3, <2>4
  <2> QED BY <2>3, <2>5, <2>6
\* ViewItem: read only, so the implication is vacuous.
<1>3 CASE req.type = "ViewItem"
  <2>1 PICK i \in IIds : req = [type |-> "ViewItem", iid |-> i]
    BY <1>3, RobustMix DEF Requests
  <2>2 p = ViewItemProgram(req, snap)
    BY <1>3 DEF ProgramFor
  <2>3 p.reads = {ItemKey(i)} /\ p.writes = {}
    BY <2>1, <2>2 DEF ViewItemProgram
  <2>4 ItemKey(i) \in Keys
    BY <2>1 DEF Keys, RowKeys
  <2> QED BY <2>3, <2>4
<1> QED BY <1>1, <1>2, <1>3


(**************************************************************************************************)
(* Initial state.  The history is empty, so every conjunct is vacuous.                            *)
(**************************************************************************************************)

LEMMA InitImpliesInv == Init => Inv
<1> SUFFICES ASSUME Init PROVE Inv
  OBVIOUS
<1>1 txnHistory = <<>> /\ clock = 0 /\ runningTxns = {}
  BY DEF Init
<1>2 Range(txnHistory) = {}
  BY <1>1 DEF Range
<1>3 CommittedTxns(txnHistory) = {}
  BY <1>2 DEF CommittedTxns
<1>4 HTypeOK
  BY <1>1 DEF HTypeOK, IsSeqStruct
<1> QED
  BY <1>1, <1>2, <1>3, <1>4
  DEF Inv, UniqueOps, TimesBounded, RunningOK, CommitKeys, BeganBefore, BodyShape, IdsOK,
      FCW, WritesKey, ReadsKey


(**************************************************************************************************)
(*                                                                                                *)
(* The inductive step: `StartAndRun`.                                                             *)
(*                                                                                                *)
(* Two events are appended, a `begin` and a `body`, both for a transaction that has no event in   *)
(* the history yet.  So the set of committed transactions is unchanged, and every conjunct about  *)
(* committed transactions carries over unexamined; what needs proving is that the two new events  *)
(* do not break uniqueness, are correctly timed, and that the body has the right shape.           *)
(*                                                                                                *)
(**************************************************************************************************)

LEMMA StartAndRunPreservesInv ==
    ASSUME Inv, NEW tid \in TxnIds, NEW req \in Requests, StartAndRun(tid, req)
    PROVE  Inv'
<1> DEFINE h    == txnHistory
            prog == ProgramFor(tid, req, dataStore)
            bOp  == [type |-> "begin", txnId |-> tid, time |-> clock + 1]
            yOp  == [type |-> "body",  txnId |-> tid,
                     reads |-> prog.reads, writes |-> prog.writes]
<1>a /\ txnHistory' = h \o <<bOp, yOp>>
     /\ clock' = clock + 1
     /\ runningTxns' = runningTxns \cup {[id |-> tid, startTime |-> clock + 1, commitTime |-> Empty]}
  BY DEF StartAndRun
<1>b ~\E op \in Range(h) : op.txnId = tid
  BY DEF StartAndRun, Unused
<1>c clock \in Nat /\ HTypeOK /\ UniqueOps(h)
  BY DEF Inv
<1>d /\ IsSeqStruct(txnHistory')
     /\ Range(txnHistory') = Range(h) \cup {bOp, yOp}
  BY <1>a, <1>c, RangeConcat2 DEF HTypeOK
\* No new commit event, so the committed set does not move.
<1>e CommittedTxns(txnHistory') = CommittedTxns(h)
  BY <1>d DEF CommittedTxns
\* No existing transaction gains a read or a write: the two new events belong to `tid`, which had
\* no event at all, so every `ReadsKey` / `WritesKey` fact about any other transaction is stable.
<1>f \A t \in CommittedTxns(h) :
        /\ \A k \in Keys : ReadsKey(txnHistory', t, k) <=> ReadsKey(h, t, k)
        /\ \A k \in Keys : WritesKey(txnHistory', t, k) <=> WritesKey(h, t, k)
  <2> SUFFICES ASSUME NEW t \in CommittedTxns(h) PROVE t # tid
    BY <1>d DEF ReadsKey, WritesKey
  <2>1 PICK op \in Range(h) : op.txnId = t /\ op.type = "commit"
    BY CommittedHasCommitOp
  <2> QED BY <2>1, <1>b
\* The two new events are for `tid`, which had no event, so uniqueness survives.
<1>u UniqueOps(txnHistory')
  <2> SUFFICES ASSUME NEW o1 \in Range(txnHistory'), NEW o2 \in Range(txnHistory'),
                      o1.txnId = o2.txnId, o1.type = o2.type
               PROVE  o1 = o2
    BY DEF UniqueOps
  <2>1 CASE o1 \in Range(h) /\ o2 \in Range(h)
    BY <2>1, <1>c DEF UniqueOps
  <2>2 CASE o1 \in {bOp, yOp} /\ o2 \in {bOp, yOp}
    BY <2>2
  <2>3 CASE o1 \in Range(h) /\ o2 \in {bOp, yOp}
    BY <2>3, <1>b
  <2>4 CASE o2 \in Range(h) /\ o1 \in {bOp, yOp}
    BY <2>4, <1>b
  <2> QED BY <1>d, <2>1, <2>2, <2>3, <2>4

\* `BeginOp` and `CommitOp` of an already committed transaction are unchanged, because the witness
\* event is still present and still unique.
<1>g \A t \in CommittedTxns(h) :
        BeginOp(txnHistory', t) = BeginOp(h, t) /\ CommitOp(txnHistory', t) = CommitOp(h, t)
  <2> SUFFICES ASSUME NEW t \in CommittedTxns(h)
               PROVE  BeginOp(txnHistory', t) = BeginOp(h, t) /\
                      CommitOp(txnHistory', t) = CommitOp(h, t)
    OBVIOUS
  <2>1 PICK c \in Range(h) : c.txnId = t /\ c.type = "commit"
    BY CommittedHasCommitOp
  <2>2 PICK b \in Range(h) : b.txnId = t /\ b.type = "begin"
    BY DEF Inv, BeganBefore
  <2>3 BeginOp(h, t) = b /\ CommitOp(h, t) = c
    BY <2>1, <2>2, <1>c, BeginOpIs, CommitOpIs
  <2>4 b \in Range(txnHistory') /\ c \in Range(txnHistory')
    BY <2>1, <2>2, <1>d
  <2>5 BeginOp(txnHistory', t) = b /\ CommitOp(txnHistory', t) = c
    BY <2>4, <1>u, <2>1, <2>2, BeginOpIs, CommitOpIs
  <2> QED BY <2>3, <2>5
\* The workload fact for the new body event.
<1>h /\ prog.reads \subseteq Keys
     /\ (prog.writes # {} => \A k \in prog.reads : \E w \in prog.writes : w.key = k)
  BY ProgramShape
<1>1 clock' \in Nat
  BY <1>a, <1>c
<1>2 HTypeOK'
  BY <1>a, <1>d DEF HTypeOK
<1>3 UniqueOps(txnHistory)'
  BY <1>u, <1>a
<1>4 TimesBounded'
  <2> SUFFICES ASSUME NEW op \in Range(txnHistory'),
                      op.type \in {"begin", "commit", "abort"}
               PROVE  op.time \in 1..clock'
    BY <1>a DEF TimesBounded
  <2>1 CASE op \in Range(h)
    BY <2>1, <1>a, <1>c DEF Inv, TimesBounded
  <2>2 CASE op = bOp
    BY <2>2, <1>a, <1>c
  <2>3 CASE op = yOp
    BY <2>3
  <2> QED BY <1>d, <2>1, <2>2, <2>3
<1>5 RunningOK'
  <2> SUFFICES ASSUME NEW r \in runningTxns'
               PROVE  /\ r.startTime \in 1..clock'
                      /\ \E op \in Range(txnHistory') :
                             op.txnId = r.id /\ op.type = "begin" /\ op.time = r.startTime
                      /\ ~\E op \in Range(txnHistory') :
                             op.txnId = r.id /\ op.type \in {"commit", "abort"}
    BY <1>a DEF RunningOK
  \* The new transaction: its begin event is `bOp`, at exactly its `startTime`.
  <2>1 CASE r = [id |-> tid, startTime |-> clock + 1, commitTime |-> Empty]
    <3>1 bOp \in Range(txnHistory') /\ bOp.txnId = tid /\ bOp.type = "begin" /\ bOp.time = clock+1
      BY <1>d
    <3>2 ~\E op \in Range(txnHistory') : op.txnId = tid /\ op.type \in {"commit", "abort"}
      BY <1>d, <1>b
    <3>3 clock + 1 \in 1..clock'
      BY <1>a, <1>c
    <3> QED BY <2>1, <3>1, <3>2, <3>3
  \* An already running transaction: its begin event survives, and the two new events are for
  \* `tid`, which is not running (it had no event at all).
  <2>2 CASE r \in runningTxns
    <3>1 r.id # tid
      BY <2>2, <1>b DEF Inv, RunningOK
    <3>2 PICK op \in Range(h) :
            op.txnId = r.id /\ op.type = "begin" /\ op.time = r.startTime
      BY <2>2 DEF Inv, RunningOK
    <3>3 op \in Range(txnHistory')
      BY <3>2, <1>d
    <3>4 ~\E o \in Range(txnHistory') : o.txnId = r.id /\ o.type \in {"commit", "abort"}
      BY <2>2, <1>d, <3>1 DEF Inv, RunningOK
    <3>5 r.startTime \in 1..clock
      BY <2>2 DEF Inv, RunningOK
    <3> QED BY <3>2, <3>3, <3>4, <3>5, <1>a, <1>c
  <2> QED BY <1>a, <2>1, <2>2
<1>6 CommitKeys'
  <2> SUFFICES ASSUME NEW op \in Range(txnHistory'), op.type = "commit", NEW k \in Keys
               PROVE  k \in op.updatedKeys <=> WritesKey(txnHistory', op.txnId, k)
    BY <1>a DEF CommitKeys
  <2>1 op \in Range(h)
    BY <1>d
  <2>2 k \in op.updatedKeys <=> WritesKey(h, op.txnId, k)
    BY <2>1 DEF Inv, CommitKeys
  \* The two new events belong to `tid`, which has no commit event, so `op.txnId # tid` and its
  \* write set is unchanged.
  <2>3 op.txnId # tid
    BY <2>1, <1>b
  <2>4 WritesKey(txnHistory', op.txnId, k) <=> WritesKey(h, op.txnId, k)
    BY <1>d, <2>3 DEF WritesKey
  <2> QED BY <2>2, <2>4
<1>7 BeganBefore'
  <2> SUFFICES ASSUME NEW t \in CommittedTxns(h)
               PROVE  \E b, c \in Range(txnHistory') :
                          /\ b.txnId = t /\ b.type = "begin"
                          /\ c.txnId = t /\ c.type = "commit"
                          /\ b.time < c.time
    BY <1>a, <1>e DEF BeganBefore
  <2>1 PICK b, c \in Range(h) :
          /\ b.txnId = t /\ b.type = "begin"
          /\ c.txnId = t /\ c.type = "commit"
          /\ b.time < c.time
    BY DEF Inv, BeganBefore
  <2> QED BY <2>1, <1>d
<1>8 BodyShape'
  <2> SUFFICES ASSUME NEW op \in Range(txnHistory'), op.type = "body", op.writes # {},
                      NEW k \in op.reads
               PROVE  \E w \in op.writes : w.key = k
    BY <1>a DEF BodyShape
  <2>1 CASE op \in Range(h)
    BY <2>1 DEF Inv, BodyShape
  <2>2 CASE op = yOp
    BY <2>2, <1>h
  <2> QED BY <1>d, <2>1, <2>2
<1>9 FCW'
  <2> SUFFICES ASSUME NEW t1 \in CommittedTxns(h), NEW t2 \in CommittedTxns(h), t1 # t2,
                      NEW k \in Keys,
                      WritesKey(txnHistory', t1, k), WritesKey(txnHistory', t2, k)
               PROVE  \/ CommitOp(txnHistory', t1).time =< BeginOp(txnHistory', t2).time
                      \/ CommitOp(txnHistory', t2).time =< BeginOp(txnHistory', t1).time
    BY <1>a, <1>e DEF FCW
  <2>1 WritesKey(h, t1, k) /\ WritesKey(h, t2, k)
    BY <1>f
  <2>2 \/ CommitOp(h, t1).time =< BeginOp(h, t2).time
       \/ CommitOp(h, t2).time =< BeginOp(h, t1).time
    BY <2>1 DEF Inv, FCW
  <2> QED BY <2>2, <1>g
<1>10 IdsOK'
  BY <1>a, <1>d DEF Inv, IdsOK
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10 DEF Inv


(**************************************************************************************************)
(*                                                                                                *)
(* The inductive step: `AbortTxn`.                                                                *)
(*                                                                                                *)
(* One `abort` event is appended and the transaction leaves `runningTxns`.  An abort event adds   *)
(* no reads, no writes and no commit, so the MVSG does not move at all; the work is confined to   *)
(* uniqueness and timing.                                                                         *)
(*                                                                                                *)
(**************************************************************************************************)

LEMMA AbortTxnPreservesInv ==
    ASSUME Inv, NEW tid \in TxnIds, AbortTxn(tid)
    PROVE  Inv'
<1> DEFINE h   == txnHistory
            aOp == [type |-> "abort", txnId |-> tid, time |-> clock + 1]
<1>a /\ txnHistory' = Append(h, aOp)
     /\ clock' = clock + 1
     /\ runningTxns' = {r \in runningTxns : r.id # tid}
  BY DEF AbortTxn
<1>b PICK rr \in runningTxns : rr.id = tid
  BY DEF AbortTxn
<1>c clock \in Nat /\ HTypeOK /\ UniqueOps(h)
  BY DEF Inv
<1>d /\ IsSeqStruct(txnHistory')
     /\ Range(txnHistory') = Range(h) \cup {aOp}
  BY <1>a, <1>c, RangeAppend DEF HTypeOK
\* A running transaction has no commit or abort event yet, which is both what makes `aOp` new and
\* what keeps `tid` out of the committed set.
<1>e ~\E op \in Range(h) : op.txnId = tid /\ op.type \in {"commit", "abort"}
  BY <1>b DEF Inv, RunningOK
<1>f CommittedTxns(txnHistory') = CommittedTxns(h)
  BY <1>d DEF CommittedTxns
\* An abort event is neither a body nor a commit, so no read or write set changes.
<1>g \A t, k : /\ (ReadsKey(txnHistory', t, k) <=> ReadsKey(h, t, k))
               /\ (WritesKey(txnHistory', t, k) <=> WritesKey(h, t, k))
  BY <1>d DEF ReadsKey, WritesKey
<1>u UniqueOps(txnHistory')
  <2> SUFFICES ASSUME NEW o1 \in Range(txnHistory'), NEW o2 \in Range(txnHistory'),
                      o1.txnId = o2.txnId, o1.type = o2.type
               PROVE  o1 = o2
    BY DEF UniqueOps
  <2>1 CASE o1 \in Range(h) /\ o2 \in Range(h)
    BY <2>1, <1>c DEF UniqueOps
  <2>2 CASE o1 = aOp /\ o2 = aOp
    BY <2>2
  <2>3 CASE o1 \in Range(h) /\ o2 = aOp
    BY <2>3, <1>e
  <2>4 CASE o2 \in Range(h) /\ o1 = aOp
    BY <2>4, <1>e
  <2> QED BY <1>d, <2>1, <2>2, <2>3, <2>4
<1>v \A t \in CommittedTxns(h) :
        BeginOp(txnHistory', t) = BeginOp(h, t) /\ CommitOp(txnHistory', t) = CommitOp(h, t)
  <2> SUFFICES ASSUME NEW t \in CommittedTxns(h)
               PROVE  BeginOp(txnHistory', t) = BeginOp(h, t) /\
                      CommitOp(txnHistory', t) = CommitOp(h, t)
    OBVIOUS
  <2>1 PICK b, c \in Range(h) :
          /\ b.txnId = t /\ b.type = "begin"
          /\ c.txnId = t /\ c.type = "commit"
    BY DEF Inv, BeganBefore
  <2>2 BeginOp(h, t) = b /\ CommitOp(h, t) = c
    BY <2>1, <1>c, BeginOpIs, CommitOpIs
  <2>3 b \in Range(txnHistory') /\ c \in Range(txnHistory')
    BY <2>1, <1>d
  <2>4 BeginOp(txnHistory', t) = b /\ CommitOp(txnHistory', t) = c
    BY <2>3, <1>u, <2>1, BeginOpIs, CommitOpIs
  <2> QED BY <2>2, <2>4
<1>1 clock' \in Nat
  BY <1>a, <1>c
<1>2 HTypeOK'
  BY <1>a, <1>d DEF HTypeOK
<1>3 UniqueOps(txnHistory)'
  BY <1>u, <1>a
<1>4 TimesBounded'
  <2> SUFFICES ASSUME NEW op \in Range(txnHistory'),
                      op.type \in {"begin", "commit", "abort"}
               PROVE  op.time \in 1..clock'
    BY <1>a DEF TimesBounded
  <2>1 CASE op \in Range(h)
    BY <2>1, <1>a, <1>c DEF Inv, TimesBounded
  <2>2 CASE op = aOp
    BY <2>2, <1>a, <1>c
  <2> QED BY <1>d, <2>1, <2>2
<1>5 RunningOK'
  <2> SUFFICES ASSUME NEW r \in runningTxns, r.id # tid
               PROVE  /\ r.startTime \in 1..clock'
                      /\ \E op \in Range(txnHistory') :
                             op.txnId = r.id /\ op.type = "begin" /\ op.time = r.startTime
                      /\ ~\E op \in Range(txnHistory') :
                             op.txnId = r.id /\ op.type \in {"commit", "abort"}
    BY <1>a DEF RunningOK
  <2>1 PICK op \in Range(h) : op.txnId = r.id /\ op.type = "begin" /\ op.time = r.startTime
    BY DEF Inv, RunningOK
  <2>2 op \in Range(txnHistory')
    BY <2>1, <1>d
  \* The only new event is `tid`'s abort, and `r.id # tid`.
  <2>3 ~\E o \in Range(txnHistory') : o.txnId = r.id /\ o.type \in {"commit", "abort"}
    BY <1>d DEF Inv, RunningOK
  <2>4 r.startTime \in 1..clock
    BY DEF Inv, RunningOK
  <2> QED BY <2>1, <2>2, <2>3, <2>4, <1>a, <1>c
<1>6 CommitKeys'
  <2> SUFFICES ASSUME NEW op \in Range(txnHistory'), op.type = "commit", NEW k \in Keys
               PROVE  k \in op.updatedKeys <=> WritesKey(txnHistory', op.txnId, k)
    BY <1>a DEF CommitKeys
  <2>1 op \in Range(h)
    BY <1>d
  <2> QED BY <2>1, <1>g DEF Inv, CommitKeys
<1>7 BeganBefore'
  <2> SUFFICES ASSUME NEW t \in CommittedTxns(h)
               PROVE  \E b, c \in Range(txnHistory') :
                          /\ b.txnId = t /\ b.type = "begin"
                          /\ c.txnId = t /\ c.type = "commit"
                          /\ b.time < c.time
    BY <1>a, <1>f DEF BeganBefore
  <2>1 PICK b, c \in Range(h) :
          /\ b.txnId = t /\ b.type = "begin"
          /\ c.txnId = t /\ c.type = "commit"
          /\ b.time < c.time
    BY DEF Inv, BeganBefore
  <2> QED BY <2>1, <1>d
<1>8 BodyShape'
  <2> SUFFICES ASSUME NEW op \in Range(txnHistory'), op.type = "body", op.writes # {},
                      NEW k \in op.reads
               PROVE  \E w \in op.writes : w.key = k
    BY <1>a DEF BodyShape
  <2>1 op \in Range(h)
    BY <1>d
  <2> QED BY <2>1 DEF Inv, BodyShape
<1>9 FCW'
  <2> SUFFICES ASSUME NEW t1 \in CommittedTxns(h), NEW t2 \in CommittedTxns(h), t1 # t2,
                      NEW k \in Keys,
                      WritesKey(txnHistory', t1, k), WritesKey(txnHistory', t2, k)
               PROVE  \/ CommitOp(txnHistory', t1).time =< BeginOp(txnHistory', t2).time
                      \/ CommitOp(txnHistory', t2).time =< BeginOp(txnHistory', t1).time
    BY <1>a, <1>f DEF FCW
  <2>1 WritesKey(h, t1, k) /\ WritesKey(h, t2, k)
    BY <1>g
  <2>2 \/ CommitOp(h, t1).time =< BeginOp(h, t2).time
       \/ CommitOp(h, t2).time =< BeginOp(h, t1).time
    BY <2>1 DEF Inv, FCW
  <2> QED BY <2>2, <1>v
<1>10 IdsOK'
  BY <1>a, <1>d DEF Inv, IdsOK
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10 DEF Inv


(**************************************************************************************************)
(*                                                                                                *)
(* The inductive step: `CommitTxn`.                                                               *)
(*                                                                                                *)
(* This is where First-Committer-Wins enters.  A `commit` event is appended, so the committing    *)
(* transaction joins `CommittedTxns`, and the `FCW` conjunct must now be established for every    *)
(* pair involving it.  The argument is exactly the guard of the action: `TxnCanCommit` says no    *)
(* transaction that committed after `tid` began has an `updatedKeys` meeting `tid`'s write set,   *)
(* and `CommitKeys` says `updatedKeys` really is the write set, so any already committed `t` that *)
(* writes a key `tid` writes must have committed at or before `tid` began.                        *)
(*                                                                                                *)
(**************************************************************************************************)

\* `KeysWrittenByTxn` and `WritesKey` are the same predicate seen two ways.
LEMMA KeysWrittenIsWritesKey ==
    ASSUME NEW h, NEW t, NEW k \in Keys
    PROVE  k \in KeysWrittenByTxn(t, h) <=> WritesKey(h, t, k)
BY DEF KeysWrittenByTxn, WritesKey

LEMMA CommitTxnPreservesInv ==
    ASSUME Inv, NEW tid \in TxnIds, CommitTxn(tid)
    PROVE  Inv'
<1> DEFINE h   == txnHistory
            cOp == [type        |-> "commit",
                    txnId       |-> tid,
                    time        |-> clock + 1,
                    updatedKeys |-> KeysWrittenByTxn(tid, h)]
<1>a /\ txnHistory' = Append(h, cOp)
     /\ clock' = clock + 1
     /\ runningTxns' = {r \in runningTxns : r.id # tid}
  BY DEF CommitTxn
<1>b PICK rr \in runningTxns :
        /\ rr.id = tid
        /\ ~\E op \in Range(h) :
               /\ op.type = "commit"
               /\ op.time > rr.startTime
               /\ KeysWrittenByTxn(tid, h) \cap op.updatedKeys /= {}
  BY DEF CommitTxn, TxnCanCommit
<1>c clock \in Nat /\ HTypeOK /\ UniqueOps(h)
  BY DEF Inv
<1>d /\ IsSeqStruct(txnHistory')
     /\ Range(txnHistory') = Range(h) \cup {cOp}
  BY <1>a, <1>c, RangeAppend DEF HTypeOK
\* `tid` is running, so it has a begin event at its `startTime` and no commit or abort event yet.
<1>e /\ ~\E op \in Range(h) : op.txnId = tid /\ op.type \in {"commit", "abort"}
     /\ rr.startTime \in 1..clock
     /\ \E op \in Range(h) : op.txnId = tid /\ op.type = "begin" /\ op.time = rr.startTime
  BY <1>b DEF Inv, RunningOK
<1>f CommittedTxns(txnHistory') = CommittedTxns(h) \cup {tid}
  BY <1>d DEF CommittedTxns
<1>g tid \notin CommittedTxns(h)
  BY <1>e DEF CommittedTxns
\* A commit event is not a body event, so no read or write set changes.
<1>k \A t, kk : /\ (ReadsKey(txnHistory', t, kk) <=> ReadsKey(h, t, kk))
                /\ (WritesKey(txnHistory', t, kk) <=> WritesKey(h, t, kk))
  BY <1>d DEF ReadsKey, WritesKey
<1>u UniqueOps(txnHistory')
  <2> SUFFICES ASSUME NEW o1 \in Range(txnHistory'), NEW o2 \in Range(txnHistory'),
                      o1.txnId = o2.txnId, o1.type = o2.type
               PROVE  o1 = o2
    BY DEF UniqueOps
  <2>1 CASE o1 \in Range(h) /\ o2 \in Range(h)
    BY <2>1, <1>c DEF UniqueOps
  <2>2 CASE o1 = cOp /\ o2 = cOp
    BY <2>2
  <2>3 CASE o1 \in Range(h) /\ o2 = cOp
    BY <2>3, <1>e
  <2>4 CASE o2 \in Range(h) /\ o1 = cOp
    BY <2>4, <1>e
  <2> QED BY <1>d, <2>1, <2>2, <2>3, <2>4
\* The begin event of the committing transaction, and its `CommitOp` in the new history.
<1>n PICK bTid \in Range(h) :
        bTid.txnId = tid /\ bTid.type = "begin" /\ bTid.time = rr.startTime
  BY <1>e
<1>o /\ BeginOp(txnHistory', tid) = bTid
     /\ CommitOp(txnHistory', tid) = cOp
  <2>1 bTid \in Range(txnHistory') /\ cOp \in Range(txnHistory')
    BY <1>n, <1>d
  <2> QED BY <2>1, <1>u, <1>n, BeginOpIs, CommitOpIs
<1>v \A t \in CommittedTxns(h) :
        BeginOp(txnHistory', t) = BeginOp(h, t) /\ CommitOp(txnHistory', t) = CommitOp(h, t)
  <2> SUFFICES ASSUME NEW t \in CommittedTxns(h)
               PROVE  BeginOp(txnHistory', t) = BeginOp(h, t) /\
                      CommitOp(txnHistory', t) = CommitOp(h, t)
    OBVIOUS
  <2>1 PICK b, c \in Range(h) :
          /\ b.txnId = t /\ b.type = "begin"
          /\ c.txnId = t /\ c.type = "commit"
    BY DEF Inv, BeganBefore
  <2>2 BeginOp(h, t) = b /\ CommitOp(h, t) = c
    BY <2>1, <1>c, BeginOpIs, CommitOpIs
  <2>3 b \in Range(txnHistory') /\ c \in Range(txnHistory')
    BY <2>1, <1>d
  <2>4 BeginOp(txnHistory', t) = b /\ CommitOp(txnHistory', t) = c
    BY <2>3, <1>u, <2>1, BeginOpIs, CommitOpIs
  <2> QED BY <2>2, <2>4
(*------------------------------------------------------------------------------------------*)
(* The First-Committer-Wins step.  Any already committed `t` sharing a written key with `tid` *)
(* committed at or before `tid` began.                                                        *)
(*------------------------------------------------------------------------------------------*)
<1>w \A t \in CommittedTxns(h) :
        (\E kk \in Keys : WritesKey(h, t, kk) /\ WritesKey(h, tid, kk)) =>
            CommitOp(h, t).time =< rr.startTime
  <2> SUFFICES ASSUME NEW t \in CommittedTxns(h), NEW kk \in Keys,
                      WritesKey(h, t, kk), WritesKey(h, tid, kk)
               PROVE  CommitOp(h, t).time =< rr.startTime
    OBVIOUS
  <2>1 PICK c \in Range(h) : c.txnId = t /\ c.type = "commit"
    BY CommittedHasCommitOp
  <2>2 CommitOp(h, t) = c
    BY <2>1, <1>c, CommitOpIs
  \* `kk` is in both `updatedKeys` and `tid`'s write set, so the guard forbids `c.time` from
  \* being after `tid` began.
  <2>3 kk \in c.updatedKeys
    BY <2>1 DEF Inv, CommitKeys
  <2>4 kk \in KeysWrittenByTxn(tid, h)
    BY KeysWrittenIsWritesKey
  <2>5 KeysWrittenByTxn(tid, h) \cap c.updatedKeys /= {}
    BY <2>3, <2>4
  <2>6 ~(c.time > rr.startTime)
    BY <2>1, <2>5, <1>b
  <2>7 c.time \in 1..clock /\ rr.startTime \in 1..clock
    BY <2>1, <1>e DEF Inv, TimesBounded
  <2> QED BY <2>2, <2>6, <2>7
<1>1 clock' \in Nat
  BY <1>a, <1>c
<1>2 HTypeOK'
  BY <1>a, <1>d DEF HTypeOK
<1>3 UniqueOps(txnHistory)'
  BY <1>u, <1>a
<1>4 TimesBounded'
  <2> SUFFICES ASSUME NEW op \in Range(txnHistory'),
                      op.type \in {"begin", "commit", "abort"}
               PROVE  op.time \in 1..clock'
    BY <1>a DEF TimesBounded
  <2>1 CASE op \in Range(h)
    BY <2>1, <1>a, <1>c DEF Inv, TimesBounded
  <2>2 CASE op = cOp
    BY <2>2, <1>a, <1>c
  <2> QED BY <1>d, <2>1, <2>2
<1>5 RunningOK'
  <2> SUFFICES ASSUME NEW r \in runningTxns, r.id # tid
               PROVE  /\ r.startTime \in 1..clock'
                      /\ \E op \in Range(txnHistory') :
                             op.txnId = r.id /\ op.type = "begin" /\ op.time = r.startTime
                      /\ ~\E op \in Range(txnHistory') :
                             op.txnId = r.id /\ op.type \in {"commit", "abort"}
    BY <1>a DEF RunningOK
  <2>1 PICK op \in Range(h) : op.txnId = r.id /\ op.type = "begin" /\ op.time = r.startTime
    BY DEF Inv, RunningOK
  <2>2 op \in Range(txnHistory')
    BY <2>1, <1>d
  <2>3 ~\E o \in Range(txnHistory') : o.txnId = r.id /\ o.type \in {"commit", "abort"}
    BY <1>d DEF Inv, RunningOK
  <2>4 r.startTime \in 1..clock
    BY DEF Inv, RunningOK
  <2> QED BY <2>1, <2>2, <2>3, <2>4, <1>a, <1>c
<1>6 CommitKeys'
  <2> SUFFICES ASSUME NEW op \in Range(txnHistory'), op.type = "commit", NEW kk \in Keys
               PROVE  kk \in op.updatedKeys <=> WritesKey(txnHistory', op.txnId, kk)
    BY <1>a DEF CommitKeys
  <2>1 CASE op \in Range(h)
    BY <2>1, <1>k DEF Inv, CommitKeys
  \* The new commit event records exactly `tid`'s write set, by construction.
  <2>2 CASE op = cOp
    BY <2>2, <1>k, KeysWrittenIsWritesKey
  <2> QED BY <1>d, <2>1, <2>2
<1>7 BeganBefore'
  <2> SUFFICES ASSUME NEW t \in CommittedTxns(h) \cup {tid}
               PROVE  \E b, c \in Range(txnHistory') :
                          /\ b.txnId = t /\ b.type = "begin"
                          /\ c.txnId = t /\ c.type = "commit"
                          /\ b.time < c.time
    BY <1>a, <1>f DEF BeganBefore
  <2>1 CASE t \in CommittedTxns(h)
    <3>1 PICK b, c \in Range(h) :
            /\ b.txnId = t /\ b.type = "begin"
            /\ c.txnId = t /\ c.type = "commit"
            /\ b.time < c.time
      BY <2>1 DEF Inv, BeganBefore
    <3> QED BY <3>1, <1>d
  \* The committing transaction began at `rr.startTime =< clock` and commits at `clock + 1`.
  <2>2 CASE t = tid
    <3>1 bTid \in Range(txnHistory') /\ cOp \in Range(txnHistory')
      BY <1>n, <1>d
    <3>2 bTid.time < cOp.time
      BY <1>n, <1>e, <1>c
    <3> QED BY <2>2, <1>n, <3>1, <3>2
  <2> QED BY <2>1, <2>2
<1>8 BodyShape'
  <2> SUFFICES ASSUME NEW op \in Range(txnHistory'), op.type = "body", op.writes # {},
                      NEW kk \in op.reads
               PROVE  \E w \in op.writes : w.key = kk
    BY <1>a DEF BodyShape
  <2>1 op \in Range(h)
    BY <1>d
  <2> QED BY <2>1 DEF Inv, BodyShape
<1>9 FCW'
  <2> SUFFICES ASSUME NEW t1 \in CommittedTxns(h) \cup {tid},
                      NEW t2 \in CommittedTxns(h) \cup {tid},
                      t1 # t2, NEW kk \in Keys,
                      WritesKey(txnHistory', t1, kk), WritesKey(txnHistory', t2, kk)
               PROVE  \/ CommitOp(txnHistory', t1).time =< BeginOp(txnHistory', t2).time
                      \/ CommitOp(txnHistory', t2).time =< BeginOp(txnHistory', t1).time
    BY <1>a, <1>f DEF FCW
  <2>0 WritesKey(h, t1, kk) /\ WritesKey(h, t2, kk)
    BY <1>k
  \* Neither is the committing transaction: the old `FCW` applies and the operators are stable.
  <2>1 CASE t1 \in CommittedTxns(h) /\ t2 \in CommittedTxns(h)
    <3>1 \/ CommitOp(h, t1).time =< BeginOp(h, t2).time
         \/ CommitOp(h, t2).time =< BeginOp(h, t1).time
      BY <2>0, <2>1 DEF Inv, FCW
    <3> QED BY <3>1, <2>1, <1>v
  \* `t2` is the committer: FCW puts `t1`'s commit at or before `tid`'s begin.
  <2>2 CASE t1 \in CommittedTxns(h) /\ t2 = tid
    <3>1 CommitOp(h, t1).time =< rr.startTime
      BY <2>0, <2>2, <1>w
    <3> QED BY <3>1, <2>2, <1>v, <1>o, <1>n
  \* `t1` is the committer: symmetric.
  <2>3 CASE t2 \in CommittedTxns(h) /\ t1 = tid
    <3>1 CommitOp(h, t2).time =< rr.startTime
      BY <2>0, <2>3, <1>w
    <3> QED BY <3>1, <2>3, <1>v, <1>o, <1>n
  <2> QED BY <2>1, <2>2, <2>3
<1>10 IdsOK'
  BY <1>a, <1>d DEF Inv, IdsOK
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10 DEF Inv


(**************************************************************************************************)
(*                                                                                                *)
(* PART 4.  THE TOP-LEVEL THEOREM                                                                 *)
(*                                                                                                *)
(**************************************************************************************************)

LEMMA NextPreservesInv == Inv /\ [Next]_vars => Inv'
<1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
  OBVIOUS
\* The stuttering case, and `AllTxnsDone`, both leave every variable `Inv` mentions unchanged.
<1>1 CASE UNCHANGED vars
  BY <1>1 DEF Inv, vars, HTypeOK, UniqueOps, TimesBounded, RunningOK, CommitKeys,
                BeganBefore, BodyShape, IdsOK, FCW, ReadsKey, WritesKey, CommittedTxns
<1>2 CASE \E tid \in TxnIds, req \in Requests : StartAndRun(tid, req)
  BY <1>2, StartAndRunPreservesInv
<1>3 CASE \E tid \in TxnIds : CommitTxn(tid)
  BY <1>3, CommitTxnPreservesInv
<1>4 CASE \E tid \in TxnIds : AbortTxn(tid)
  BY <1>4, AbortTxnPreservesInv
<1> QED BY <1>1, <1>2, <1>3, <1>4 DEF Next

THEOREM InvIsInductive == Spec => []Inv
<1>1 Init => Inv
  BY InitImpliesInv
<1>2 Inv /\ [Next]_vars => Inv'
  BY NextPreservesInv
<1> QED BY <1>1, <1>2, PTL DEF Spec

(**************************************************************************************************)
(*                                                                                                *)
(* The result: under the robust mix (StoreBid + ViewItem), every reachable history is conflict    *)
(* serializable.                                                                                  *)
(*                                                                                                *)
(* The finiteness side condition is immediate: committed transactions are drawn from `TxnIds`,    *)
(* which is `1..NumTxns`.                                                                         *)
(*                                                                                                *)
(**************************************************************************************************)

LEMMA CommittedFinite ==
    ASSUME Inv
    PROVE  IsFiniteSet(CommittedTxns(txnHistory))
<1>1 CommittedTxns(txnHistory) \subseteq TxnIds
  <2> SUFFICES ASSUME NEW t \in CommittedTxns(txnHistory) PROVE t \in TxnIds
    OBVIOUS
  <2>1 PICK c \in Range(txnHistory) : c.txnId = t /\ c.type = "commit"
    BY CommittedHasCommitOp
  <2> QED BY <2>1 DEF Inv, IdsOK
<1>2 IsFiniteSet(TxnIds)
  BY NumTxnsNat, FS_Interval DEF TxnIds
<1> QED BY <1>1, <1>2, FS_Subset

THEOREM Serializable == Spec => []SerializableViaPath
<1>1 Inv => SerializableViaPath
  BY InvImpliesMVSGOK, CommittedFinite, MVSGOKImpliesSerializable
     DEF SerializableViaPath
<1> QED BY InvIsInductive, <1>1, PTL

====================================================================================================
