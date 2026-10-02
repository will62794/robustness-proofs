---------------------------- MODULE Auction_Proofs ----------------------------
(***************************************************************************)
(* A TLAPS proof that SerializableViaPath is an invariant of Auction, for  *)
(* the robust transaction mix of Bernardi & Gotsman: any subset of         *)
(* StoreBid, ViewItem and ViewUsers (i.e. RegUser disabled; with RegUser   *)
(* enabled the property is false, as the spec itself explains).            *)
(*                                                                         *)
(* Proof idea.  Give every committed transaction t a position              *)
(*                                                                         *)
(*     Pos(t) = commit time of t   if t writes some key,                   *)
(*            = begin time of t    if t is read-only,                      *)
(*                                                                         *)
(* and show every serialization-graph edge t1 -> t2 has Pos(t1) < Pos(t2), *)
(* so the graph is acyclic.  WW and WR edges are immediate.  An RW edge    *)
(* from a read-only t1 is fine since t1 began before t2 committed.  The    *)
(* only updater is StoreBid, which reads only ITEMS(iid) and also writes   *)
(* it, so an RW edge from an updater is a write-write conflict, and        *)
(* First-Committer-Wins forces t1 to commit before t2.                     *)
(***************************************************************************)
EXTENDS Auction, TLAPS, SequenceTheorems, NaturalsInduction

ASSUME NoRegUser == "RegUser" \notin EnabledTxnTypes

(***************************************************************************)
(* Notation                                                                *)
(***************************************************************************)

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

\* Every body is either read-only or reads only keys it also writes.
BodyOK(B) == B.writes = {} \/ RNWB(B) = {}

(***************************************************************************)
(* The inductive invariant.                                                *)
(***************************************************************************)

TypeInv ==
    /\ clock \in Nat
    /\ txnHistory \in Seq(Ops(txnHistory))
    /\ DOMAIN txnProg = TxnIds
    /\ DOMAIN txnReq = TxnIds

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

BodyInv ==
    \A t \in TxnIds : Started(txnHistory, t) => BodyOK(txnProg[t])

RWInv ==
    \A t1, t2 \in TxnIds :
        /\ Committed(txnHistory, t1) /\ Committed(txnHistory, t2) /\ t1 # t2
        /\ KW(txnProg, t1) # {}
        /\ \E k \in KW(txnProg, t2) : k \in txnProg[t1].reads
        /\ BT(txnHistory, t1) < CT(txnHistory, t2)
        => CT(txnHistory, t1) < CT(txnHistory, t2)

Inv == TypeInv /\ HistInv /\ BodyInv /\ RWInv

----------------------------------------------------------------------------
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
(* The auction programs.                                                   *)
(***************************************************************************)

LEMMA ProgOK ==
    ASSUME NEW tid, NEW req \in Requests, NEW snap
    PROVE  BodyOK(ProgramFor(tid, req, snap))
  <1>0. req.type \in {"ViewUsers", "StoreBid", "ViewItem"}
    BY NoRegUser DEF Requests
  <1>1. CASE req.type = "ViewUsers"
    <2>1. ProgramFor(tid, req, snap) = ViewUsersProgram(req, snap)
      BY <1>1 DEF ProgramFor
    <2> QED
      BY <2>1 DEF ViewUsersProgram, BodyOK
  <1>2. CASE req.type = "ViewItem"
    <2>1. ProgramFor(tid, req, snap) = ViewItemProgram(req, snap)
      BY <1>2 DEF ProgramFor
    <2> QED
      BY <2>1 DEF ViewItemProgram, BodyOK
  <1>3. CASE req.type = "StoreBid"
    <2>1. ProgramFor(tid, req, snap) = StoreBidProgram(tid, req, snap)
      BY <1>3 DEF ProgramFor
    <2>2. req.iid \in IIds
      BY <1>3 DEF Requests
    <2>3. ItemKey(req.iid) \in Keys
      BY <2>2 DEF Keys, RowKeys
    <2> DEFINE B == StoreBidProgram(tid, req, snap)
    <2>4. B.reads = {ItemKey(req.iid)}
      BY DEF StoreBidProgram
    <2>5. \E wop \in B.writes : wop.key = ItemKey(req.iid)
      BY DEF StoreBidProgram
    <2>6. RNWB(B) = {}
      BY <2>3, <2>4, <2>5 DEF RNWB, KWB
    <2> QED
      BY <2>1, <2>6 DEF BodyOK
  <1> QED
    BY <1>0, <1>1, <1>2, <1>3

----------------------------------------------------------------------------
(***************************************************************************)
(* The initial state.                                                      *)
(***************************************************************************)

THEOREM InitInv ==
    Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1>1. Ops(txnHistory) = {}
    BY DEF Init, Ops, SI!Range
  <1>2. TypeInv
    <2>2. txnHistory \in Seq(Ops(txnHistory))
      BY EmptySeq DEF Init
    <2> QED
      BY <2>2 DEF Init, TypeInv
  <1>3. HistInv
    BY <1>1 DEF HistInv, Init, Started
  <1>4. BodyInv
    BY <1>1 DEF BodyInv, Started
  <1>6. RWInv
    BY <1>1 DEF RWInv, Committed
  <1> QED
    BY <1>2, <1>3, <1>4, <1>6 DEF Inv

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
        /\ UNCHANGED <<txnProg, txnReq>>
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
    <2> SUFFICES ASSUME NEW op1 \in Ops(h'), NEW op2 \in Ops(h'),
                        op1.txnId = op2.txnId, op1.type = op2.type
                 PROVE  op1 = op2
      BY DEF UniqueOps
    <2>1. CASE op1 \in Ops(h) /\ op2 \in Ops(h)
      BY <2>1 DEF HistInv
    <2>2. CASE op1 \in Ops(h) /\ op2 \notin Ops(h)
      BY <2>2, <1>2, <1>1 DEF Aborted
    <2>3. CASE op1 \notin Ops(h) /\ op2 \in Ops(h)
      BY <2>3, <1>2, <1>1 DEF Aborted
    <2>4. CASE op1 \notin Ops(h) /\ op2 \notin Ops(h)
      BY <2>4, <1>1
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4
  <1>4. /\ \A t : Started(h', t) <=> Started(h, t)
        /\ \A t : Committed(h', t) <=> Committed(h, t)
        /\ \A t : Aborted(h', t) <=> (Aborted(h, t) \/ t = tid)
    <2>1. \A t : Started(h', t) <=> Started(h, t)
      BY <1>1, <1>2 DEF Started
    <2>2. \A t : Committed(h', t) <=> Committed(h, t)
      BY <1>1 DEF Committed
    <2>3. \A t : Aborted(h', t) <=> (Aborted(h, t) \/ t = tid)
      BY <1>1 DEF Aborted
    <2> QED
      BY <2>1, <2>2, <2>3
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
        <4>2. op.type \in {"begin", "commit", "abort"} => op.time \in Nat /\ op.time =< clock'
          BY <3>2, <1>0 DEF HistInv, TypeInv
        <4>3. op.type = "commit" => BT(h', op.txnId) < op.time
          BY <3>2, <4>1, <1>5 DEF HistInv
        <4> QED
          BY <3>2, <4>2, <4>3, <1>0 DEF HistInv
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
  <1>13. BodyInv'
    BY <1>0, <1>4 DEF BodyInv
  <1>15. RWInv'
    <2> SUFFICES ASSUME NEW t1 \in TxnIds, NEW t2 \in TxnIds,
                        Committed(h', t1), Committed(h', t2), t1 # t2,
                        KW(txnProg', t1) # {},
                        \E k \in KW(txnProg', t2) : k \in txnProg'[t1].reads,
                        BT(h', t1) < CT(h', t2)
                 PROVE  CT(h', t1) < CT(h', t2)
      BY DEF RWInv
    <2>1. Committed(h, t1) /\ Committed(h, t2) /\ Started(h, t1)
      BY <1>4 DEF Committed, Started
    <2>2. BT(h', t1) = BT(h, t1) /\ CT(h', t1) = CT(h, t1) /\ CT(h', t2) = CT(h, t2)
      BY <2>1, <1>5, <1>6
    <2> QED
      BY <2>1, <2>2, <1>0 DEF RWInv
  <1> QED
    BY <1>9, <1>10, <1>13, <1>15

----------------------------------------------------------------------------
(***************************************************************************)
(* StartAndRun preserves the invariant.                                    *)
(***************************************************************************)

THEOREM StartStep ==
    ASSUME Inv, NEW tid \in TxnIds, NEW req \in Requests, StartAndRun(tid, req)
    PROVE  Inv'
  <1> DEFINE h == txnHistory
             B == ProgramFor(tid, req, dataStore)
             bop == [type |-> "begin", txnId |-> tid, time |-> clock + 1]
             bdy == [type |-> "body", txnId |-> tid, reads |-> B.reads, writes |-> B.writes]
             newTxn == [id |-> tid, startTime |-> clock + 1, commitTime |-> Empty]
  <1> USE DEF Inv
  <1>0. /\ ~Started(h, tid)
        /\ txnProg' = [txnProg EXCEPT ![tid] = B]
        /\ h' = h \o <<bop, bdy>>
        /\ runningTxns' = runningTxns \cup {newTxn}
        /\ clock' = clock + 1
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
                                       /\ KW(txnProg', t) = KW(txnProg, t)
        /\ txnProg'[tid] = B
    BY <1>0 DEF TypeInv, KW
  <1>a. \A t : Started(h, t) => t \in TxnIds /\ t # tid
    BY <1>0 DEF HistInv, Started
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
  <1>14. BodyInv'
    <2> SUFFICES ASSUME NEW t \in TxnIds, Started(h', t)
                 PROVE  BodyOK(txnProg'[t])
      BY DEF BodyInv
    <2>1. CASE t = tid
      BY <2>1, <1>6, ProgOK
    <2>2. CASE t # tid
      BY <2>2, <1>3, <1>6 DEF BodyInv
    <2> QED
      BY <2>1, <2>2
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
    BY <1>10, <1>11, <1>14, <1>16

----------------------------------------------------------------------------
(***************************************************************************)
(* CommitTxn preserves the invariant.                                      *)
(***************************************************************************)

THEOREM CommitStep ==
    ASSUME Inv, NEW tid \in TxnIds, CommitTxn(tid)
    PROVE  Inv'
  <1> DEFINE h == txnHistory
             KWT == KW(txnProg, tid)
             cop == [type |-> "commit", txnId |-> tid, time |-> clock + 1, updatedKeys |-> KWT]
  <1> USE DEF Inv
  <1>a. /\ tid \in RunIds(runningTxns)
        /\ Started(h, tid) /\ ~Committed(h, tid) /\ ~Aborted(h, tid)
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
        /\ runningTxns' = {r \in runningTxns : r.id # tid}
        /\ clock' = clock + 1
        /\ UNCHANGED <<txnProg, txnReq>>
    BY <1>b DEF CommitTxn, SI!CommitTxn
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
  <1>15. BodyInv'
    BY <1>0, <1>3 DEF BodyInv
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
        <4>2. txnProg[tid].writes # {}
          BY <2>3, <1>0 DEF KW, KWB
        <4>3. BodyOK(txnProg[tid])
          BY <1>a DEF BodyInv
        <4> QED
          BY <4>1, <4>2, <4>3 DEF BodyOK
      <3> QED
        BY <3>6, <3>7
    <2> QED
      BY <2>1, <2>2, <2>3
  <1> QED
    BY <1>11, <1>12, <1>15, <1>17

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
    BY <1>4 DEF vars, Inv, TypeInv, HistInv, BodyInv, RWInv,
                Ops, Started, Committed, Aborted, BT, CT, KW, RunIds
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
