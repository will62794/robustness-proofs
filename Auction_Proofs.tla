----------------------------- MODULE Auction_Proofs -----------------------------
(**************************************************************************************************)
(*                                                                                                *)
(* TLAPS proof development for  Spec => [](SerializableViaPath)  of the auction application.       *)
(*                                                                                                *)
(* SCOPE.  The result is FALSE for the full auction workload: two concurrent `RegUser`s that       *)
(* request the same nickname miss each other's uniqueness check and both insert, which is the      *)
(* write skew of the paper's Figure 2(d) and a genuine non-serializable history (config            *)
(* `auction-reguser` finds it).  So this module carries an explicit assumption restricting the     *)
(* workload to the ROBUST mix, `EnabledTxnTypes \subseteq {"StoreBid", "ViewItem"}` -- the mix     *)
(* Bernardi & Gotsman prove robust in their Sections 2 and 6, and the `auction-robust` config.     *)
(*                                                                                                *)
(* THE ARGUMENT.                                                                                  *)
(*                                                                                                *)
(* Fekete et al. prove SI-serializability by ruling out the "dangerous structure" -- two           *)
(* consecutive rw-anti-dependency edges around a cycle.  For this workload there is a sharper and  *)
(* much more mechanisable argument: the serialization graph carries a strictly increasing integer  *)
(* RANK, so it is acyclic outright, with no cycle analysis at all.                                 *)
(*                                                                                                *)
(*     rank(t)  ==  IF t writes anything THEN commit(t) ELSE begin(t)                              *)
(*                                                                                                *)
(* i.e. read-only transactions are ranked by when they started, updaters by when they committed.   *)
(* Three properties of the history make every MVSG edge increase this rank:                        *)
(*                                                                                                *)
(*   H1  `LifetimeOK`       begin(t) < commit(t) for every committed t.                            *)
(*   H2  `ReadsSubsumed`    a transaction that writes only reads keys that it also writes.         *)
(*   H3  `FCWDisjoint`      two distinct committed transactions that write a common key have       *)
(*                          disjoint lifetimes (this is First-Committer-Wins).                     *)
(*                                                                                                *)
(* H2 is where the workload enters, and it is the whole of the robustness content:                 *)
(*                                                                                                *)
(*   * StoreBid(i) reads ITEM(i) and writes ITEM(i) (and a fresh, never-read BID key).  Its only   *)
(*     read is of a key it writes.                                                                 *)
(*   * ViewItem(i) writes nothing, so the implication is vacuous.                                  *)
(*   * RegUser VIOLATES it: it scans every USER key but writes only one of them.  That is exactly  *)
(*     the predicate read with no matching write, and exactly why RegUser is not robust.           *)
(*                                                                                                *)
(* Why the three suffice, edge by edge (`EdgeIncreasesRank` below):                                *)
(*                                                                                                *)
(*   ww(t1,t2)  gives commit(t1) < commit(t2) directly, and both transactions write.               *)
(*   wr(t1,t2)  gives commit(t1) < begin(t2) =< rank(t2) by H1, and t1 writes.                     *)
(*   rw(t1,t2)  gives only begin(t1) < commit(t2), which is NOT enough on its own -- this is the   *)
(*              edge write skew rides on.  Two cases:                                              *)
(*                t1 read-only: rank(t1) = begin(t1) < commit(t2) = rank(t2).  Done.               *)
(*                t1 writes:    t1 read the key that t2 wrote, so by H2 t1 wrote it too.  Then t1  *)
(*                              and t2 share a written key, so by H3 their lifetimes are disjoint, *)
(*                              and begin(t1) < commit(t2) forces commit(t1) < begin(t2).  The     *)
(*                              rw edge is thereby upgraded to a ww-style ordering.                *)
(*                                                                                                *)
(* The last case is the structural reason the mix is robust.  An rw edge out of an UPDATER is      *)
(* never really an anti-dependency here: First-Committer-Wins has already serialized the two       *)
(* transactions.  Only read-only transactions emit genuine anti-dependency edges, and a read-only  *)
(* transaction has no outgoing ww or wr edges, so no cycle can be closed through one.              *)
(*                                                                                                *)
(**************************************************************************************************)
EXTENDS Auction, TLAPS, SequenceTheorems, NaturalsInduction

(**************************************************************************************************)
(* The robust mix.  See SCOPE above.                                                              *)
(**************************************************************************************************)
ASSUME RobustMix == EnabledTxnTypes \subseteq {"StoreBid", "ViewItem"}

----------------------------------------------------------------------------------------------------
(**************************************************************************************************)
(*                                                                                                *)
(* Part 1.  The base case: the empty history is serializable.                                     *)
(*                                                                                                *)
(**************************************************************************************************)

LEMMA EmptyRange == SI!Range(<<>>) = {}
  BY DEF SI!Range

LEMMA EmptyCommitted == SI!CommittedTxns(<<>>) = {}
  BY EmptyRange DEF SI!CommittedTxns

LEMMA EmptyGraph == SI!SerializationGraph(<<>>) = {}
  BY EmptyCommitted DEF SI!SerializationGraph

LEMMA EmptyPaths == SI!Paths({}) = {}
  BY DEF SI!Paths, SI!GraphNodes

LEMMA EmptyNoCycle == SI!IsCycleViaPath({}) = FALSE
  BY EmptyPaths DEF SI!IsCycleViaPath

THEOREM Base == Init => SerializableViaPath
PROOF
  <1>1. Init => txnHistory = <<>> BY DEF Init
  <1>2. Init => SI!SerializationGraph(txnHistory) = {} BY <1>1, EmptyGraph
  <1>3. Init => SI!IsCycleViaPath(SI!SerializationGraph(txnHistory)) = FALSE
         BY <1>2, EmptyNoCycle
  <1>4. QED BY <1>3 DEF SerializableViaPath, SI!IsConflictSerializableViaPath

----------------------------------------------------------------------------------------------------
(**************************************************************************************************)
(*                                                                                                *)
(* Part 2.  A graph with a strictly increasing rank has no cycle.                                 *)
(*                                                                                                *)
(* This is generic graph theory, independent of snapshot isolation: if some integer-valued `rank` *)
(* strictly increases along every edge, then no path can return to its start, because rank would  *)
(* have to strictly increase from a node back to itself.                                          *)
(*                                                                                                *)
(* The induction is over the position along the path, using `NatInduction`.                        *)
(*                                                                                                *)
(**************************************************************************************************)

(*------------------------------------------------------------------------------------------*)
(* Unpacking `SI!Paths`.  A path is a function on 1..n for some n >= 1, all of whose values   *)
(* are graph nodes and whose consecutive pairs are edges.                                     *)
(*------------------------------------------------------------------------------------------*)
LEMMA PathShape ==
  ASSUME NEW edges, NEW p \in SI!Paths(edges)
  PROVE  /\ Len(p) \in Nat \ {0}
         /\ DOMAIN p = 1..Len(p)
         /\ \A i \in 1..(Len(p)-1) : <<p[i], p[i+1]>> \in edges
PROOF
  <1> DEFINE nodes == SI!GraphNodes(edges)
  \* The length bound in `SI!Paths` is `SI!Cardinality(nodes) + 1`, but its actual value is
  \* irrelevant here: all we need is that SOME positive n bounds the path, so we leave the
  \* bound existentially quantified rather than naming it (naming it with `Cardinality`
  \* rather than `SI!Cardinality` is what tripped the prover up).
  <1>1. PICK n \in Nat \ {0} : p \in [1..n -> nodes]
    <2> DEFINE Lens == 1..(SI!Cardinality(nodes) + 1)
    <2>1. p \in UNION {[1..k -> nodes] : k \in Lens}
      BY DEF SI!Paths
    <2>2. PICK X \in {[1..k -> nodes] : k \in Lens} : p \in X
      BY <2>1
    <2>3. PICK k \in Lens : p \in [1..k -> nodes]
      BY <2>2
    \* `Lens` is an integer interval starting at 1, so any member is a positive integer.
    <2>4. k \in Nat \ {0}
      <3>1. k \in Int /\ 1 =< k BY <2>3
      <3>2. QED BY <3>1
    <2>5. QED BY <2>2, <2>3
  <1>3. p \in Seq(nodes)
    BY <1>1, SeqDef
  <1>4. Len(p) = n
    <2>1. DOMAIN p = 1..n BY <1>1
    <2>2. DOMAIN p = 1..Len(p) BY <1>3, LenProperties
    <2>3. Len(p) \in Nat BY <1>3, LenProperties
    <2>4. QED BY <1>1, <2>1, <2>2, <2>3
  <1>5. \A i \in 1..(Len(p)-1) : <<p[i], p[i+1]>> \in edges
    BY <1>4 DEF SI!Paths
  <1>6. QED BY <1>1, <1>3, <1>4, <1>5, LenProperties

(*------------------------------------------------------------------------------------------*)
(* The rank lemma.                                                                            *)
(*------------------------------------------------------------------------------------------*)
LEMMA NoCycleByRank ==
  ASSUME NEW edges, NEW rank(_),
         \A e \in edges : /\ rank(e[1]) \in Nat
                          /\ rank(e[2]) \in Nat
                          /\ rank(e[1]) < rank(e[2])
  PROVE  ~SI!IsCycleViaPath(edges)
PROOF
  <1> SUFFICES ASSUME SI!IsCycleViaPath(edges) PROVE FALSE
    OBVIOUS
  <1>1. PICK p \in SI!Paths(edges) : Len(p) > 1 /\ p[1] = p[Len(p)]
    BY DEF SI!IsCycleViaPath
  <1>2. /\ Len(p) \in Nat \ {0}
        /\ \A i \in 1..(Len(p)-1) : <<p[i], p[i+1]>> \in edges
    BY <1>1, PathShape
  \* Each consecutive pair is an edge, so rank strictly increases by one step.
  <1>3. \A i \in 1..(Len(p)-1) : /\ rank(p[i])   \in Nat
                                 /\ rank(p[i+1]) \in Nat
                                 /\ rank(p[i]) < rank(p[i+1])
    <2>1. SUFFICES ASSUME NEW i \in 1..(Len(p)-1)
                   PROVE  /\ rank(p[i])   \in Nat
                          /\ rank(p[i+1]) \in Nat
                          /\ rank(p[i]) < rank(p[i+1])
      OBVIOUS
    <2>2. <<p[i], p[i+1]>> \in edges BY <1>2
    <2>3. <<p[i], p[i+1]>>[1] = p[i] /\ <<p[i], p[i+1]>>[2] = p[i+1] OBVIOUS
    <2>4. QED BY <2>2, <2>3
  \* Induct along the path: rank(p[1]) < rank(p[m]) for every later position m.
  <1> DEFINE Q(m) == (m \in 2..Len(p)) => /\ rank(p[1]) \in Nat
                                          /\ rank(p[m]) \in Nat
                                          /\ rank(p[1]) < rank(p[m])
  <1>4. Q(0) OBVIOUS
  <1>5. \A m \in Nat : Q(m) => Q(m+1)
    <2>1. SUFFICES ASSUME NEW m \in Nat, Q(m), (m+1) \in 2..Len(p)
                   PROVE  /\ rank(p[1]) \in Nat
                          /\ rank(p[m+1]) \in Nat
                          /\ rank(p[1]) < rank(p[m+1])
      OBVIOUS
    <2>2. m \in 1..(Len(p)-1) BY <2>1, <1>2
    <2>3. /\ rank(p[m])   \in Nat
          /\ rank(p[m+1]) \in Nat
          /\ rank(p[m]) < rank(p[m+1])
      BY <2>2, <1>3
    <2>4. CASE m = 1
      BY <2>3, <2>4
    <2>5. CASE m # 1
      <3>1. m \in 2..Len(p) BY <2>2, <2>5, <1>2
      <3>2. /\ rank(p[1]) \in Nat
            /\ rank(p[m]) \in Nat
            /\ rank(p[1]) < rank(p[m])
        BY <3>1, <2>1
      <3>3. QED BY <3>2, <2>3
    <2>6. QED BY <2>4, <2>5
  <1>6. \A m \in Nat : Q(m)
    <2> HIDE DEF Q
    <2>1. QED BY <1>4, <1>5, NatInduction
  \* Apply it at the far end of the cycle, which is the same node as the near end.
  <1>7. Len(p) \in 2..Len(p) BY <1>1, <1>2
  <1>8. rank(p[1]) < rank(p[Len(p)]) BY <1>6, <1>7
  <1>9. QED BY <1>8, <1>1, <1>6, <1>7

----------------------------------------------------------------------------------------------------
(**************************************************************************************************)
(*                                                                                                *)
(* Part 3.  The three history properties, and the fact that they make the rank increase.          *)
(*                                                                                                *)
(* These are stated over an arbitrary history `h` so that the mathematics is separated from the   *)
(* spec.  Part 5 discharges them as invariants of `Spec`.                                         *)
(*                                                                                                *)
(**************************************************************************************************)

\* Shorthands for the begin and commit times of a transaction in a history.
Begin(h, t)  == SI!BeginOp(h, t).time
Commit(h, t) == SI!CommitOp(h, t).time

\* Does `t` write anything at all in `h`?  Updaters are ranked by commit time, read-only
\* transactions by begin time.
Updater(h, t) == SI!WritesByTxn(h, t) # {}

Rank(h, t) == IF Updater(h, t) THEN Commit(h, t) ELSE Begin(h, t)

(*------------------------------------------------------------------------------------------*)
(* H1.  Every committed transaction has natural begin and commit times, and began strictly    *)
(* before it committed.  (The clock ticks on both events, so the times differ.)                *)
(*------------------------------------------------------------------------------------------*)
LifetimeOK(h) ==
  \A t \in SI!CommittedTxns(h) :
    /\ Begin(h, t)  \in Nat
    /\ Commit(h, t) \in Nat
    /\ Begin(h, t) < Commit(h, t)

(*------------------------------------------------------------------------------------------*)
(* H2.  A transaction that writes anything reads only keys that it also writes.                *)
(*                                                                                            *)
(* This is the workload property that makes the mix robust.  StoreBid satisfies it (it reads   *)
(* only ITEM(i), which it writes); ViewItem satisfies it vacuously (no writes); RegUser does    *)
(* NOT (it scans all of USERS but writes one key).                                             *)
(*------------------------------------------------------------------------------------------*)
ReadsSubsumed(h) ==
  \A t \in SI!CommittedTxns(h) :
    Updater(h, t) =>
      \A rop \in SI!ReadsByTxn(h, t) :
        \E wop \in SI!WritesByTxn(h, t) : wop.key = rop.key

(*------------------------------------------------------------------------------------------*)
(* H3.  First-Committer-Wins: two distinct committed transactions that write a common key      *)
(* cannot have overlapping lifetimes.                                                          *)
(*                                                                                            *)
(* Note the non-strict `=<`.  The natural reading of "disjoint lifetimes" would use `<`, but   *)
(* the weaker form is all the rank argument needs (in the rw case the target always writes, so *)
(* H1 supplies the missing strictness), and proving it avoids having to establish that all     *)
(* event times are distinct -- an extra clock invariant that would otherwise be needed.        *)
(*------------------------------------------------------------------------------------------*)
FCWDisjoint(h) ==
  \A t1, t2 \in SI!CommittedTxns(h) :
    (t1 # t2) =>
      ((\E w1 \in SI!WritesByTxn(h, t1), w2 \in SI!WritesByTxn(h, t2) : w1.key = w2.key)
        => \/ Commit(h, t1) =< Begin(h, t2)
           \/ Commit(h, t2) =< Begin(h, t1))

HistoryOK(h) == LifetimeOK(h) /\ ReadsSubsumed(h) /\ FCWDisjoint(h)

(*------------------------------------------------------------------------------------------*)
(* The core step: under H1-H3, every MVSG edge strictly increases `Rank`.                     *)
(*------------------------------------------------------------------------------------------*)
LEMMA EdgeIncreasesRank ==
  ASSUME NEW h, HistoryOK(h),
         NEW e \in SI!SerializationGraph(h)
  PROVE  /\ Rank(h, e[1]) \in Nat
         /\ Rank(h, e[2]) \in Nat
         /\ Rank(h, e[1]) < Rank(h, e[2])
PROOF
  <1> DEFINE C  == SI!CommittedTxns(h)
             t1 == e[1]
             t2 == e[2]
  <1>1. /\ t1 \in C
        /\ t2 \in C
        /\ t1 # t2
        /\ \/ SI!WWDependency(h, t1, t2)
           \/ SI!WRDependency(h, t1, t2)
           \/ SI!RWDependency(h, t1, t2)
    BY DEF SI!SerializationGraph
  \* Both endpoints have natural, ordered begin/commit times, hence natural ranks.
  <1>2. /\ Begin(h, t1) \in Nat /\ Commit(h, t1) \in Nat /\ Begin(h, t1) < Commit(h, t1)
        /\ Begin(h, t2) \in Nat /\ Commit(h, t2) \in Nat /\ Begin(h, t2) < Commit(h, t2)
    BY <1>1 DEF HistoryOK, LifetimeOK
  <1>3. Rank(h, t1) \in Nat /\ Rank(h, t2) \in Nat
    BY <1>2 DEF Rank
  \* `Rank` never exceeds the commit time, and is at least the begin time.
  <1>4. /\ Begin(h, t2) =< Rank(h, t2)
        /\ Rank(h, t1) =< Commit(h, t1)
    BY <1>2 DEF Rank
  \* Case ww: both endpoints write, so both are ranked by commit time.
  <1>5. CASE SI!WWDependency(h, t1, t2)
    <2>1. PICK op1 \in SI!WritesByTxn(h, t1), op2 \in SI!WritesByTxn(h, t2) :
             Commit(h, t1) < Commit(h, t2)
      BY <1>5 DEF SI!WWDependency, Commit
    <2>2. Updater(h, t1) /\ Updater(h, t2) BY <2>1 DEF Updater
    <2>3. QED BY <2>1, <2>2, <1>3 DEF Rank
  \* Case wr: t1 writes (so is ranked by commit), and committed before t2 even began.
  <1>6. CASE SI!WRDependency(h, t1, t2)
    <2>1. PICK op1 \in SI!WritesByTxn(h, t1), op2 \in SI!ReadsByTxn(h, t2) :
             Commit(h, t1) < Begin(h, t2)
      BY <1>6 DEF SI!WRDependency, Commit, Begin
    <2>2. Updater(h, t1) BY <2>1 DEF Updater
    <2>3. Rank(h, t1) = Commit(h, t1) BY <2>2 DEF Rank
    <2>4. QED BY <2>1, <2>3, <1>4, <1>2, <1>3
  \* Case rw: the interesting one.  t2 writes, so is ranked by commit time; t1 read that key.
  <1>7. CASE SI!RWDependency(h, t1, t2)
    <2>1. PICK rop \in SI!ReadsByTxn(h, t1), wop \in SI!WritesByTxn(h, t2) :
             /\ rop.key = wop.key
             /\ Begin(h, t1) < Commit(h, t2)
      BY <1>7 DEF SI!RWDependency, Commit, Begin
    <2>2. Updater(h, t2) BY <2>1 DEF Updater
    <2>3. Rank(h, t2) = Commit(h, t2) BY <2>2 DEF Rank
    \* Subcase (a): t1 is read-only.  Its rank is its begin time, which the edge already bounds.
    <2>4. CASE ~Updater(h, t1)
      <3>1. Rank(h, t1) = Begin(h, t1) BY <2>4 DEF Rank
      <3>2. QED BY <3>1, <2>3, <2>1, <1>3
    \* Subcase (b): t1 also writes.  By H2 it wrote the very key it read, so t1 and t2 share a
    \* written key; by H3 their lifetimes are disjoint; and the edge rules out t2 finishing first.
    <2>5. CASE Updater(h, t1)
      <3>1. PICK w1 \in SI!WritesByTxn(h, t1) : w1.key = rop.key
        BY <2>5, <1>1 DEF HistoryOK, ReadsSubsumed
      <3>2. \E a \in SI!WritesByTxn(h, t1), b \in SI!WritesByTxn(h, t2) : a.key = b.key
        BY <3>1, <2>1
      <3>3. \/ Commit(h, t1) =< Begin(h, t2)
            \/ Commit(h, t2) =< Begin(h, t1)
        BY <3>2, <1>1 DEF HistoryOK, FCWDisjoint
      \* The second disjunct contradicts the edge: it would put commit(t2) at or before
      \* begin(t1), while the rw edge says begin(t1) strictly precedes commit(t2).
      <3>4. ~(Commit(h, t2) =< Begin(h, t1))
        BY <2>1, <1>2
      <3>5. Commit(h, t1) =< Begin(h, t2) BY <3>3, <3>4
      <3>6. Rank(h, t1) = Commit(h, t1) BY <2>5 DEF Rank
      \* H1 supplies the strictness the weakened H3 does not:
      \*   rank(t1) = commit(t1) =< begin(t2) < commit(t2) = rank(t2).
      <3>7. QED BY <3>5, <3>6, <2>3, <1>2, <1>3
    <2>6. QED BY <2>4, <2>5
  <1>8. QED BY <1>1, <1>3, <1>5, <1>6, <1>7

(*------------------------------------------------------------------------------------------*)
(* H1-H3 therefore imply conflict serializability, with no cycle analysis at all.             *)
(*------------------------------------------------------------------------------------------*)
THEOREM HistoryOKImpliesSerializable ==
  ASSUME NEW h, HistoryOK(h)
  PROVE  SI!IsConflictSerializableViaPath(h)
PROOF
  <1> DEFINE G == SI!SerializationGraph(h)
             rk(t) == Rank(h, t)
  <1>1. \A e \in G : rk(e[1]) \in Nat /\ rk(e[2]) \in Nat /\ rk(e[1]) < rk(e[2])
    BY EdgeIncreasesRank
  <1>2. ~SI!IsCycleViaPath(G)
    <2> HIDE DEF rk, G
    <2>1. QED BY <1>1, NoCycleByRank
  <1>3. QED BY <1>2 DEF SI!IsConflictSerializableViaPath

----------------------------------------------------------------------------------------------------
(**************************************************************************************************)
(*                                                                                                *)
(* Part 4.  The workload lemma: the auction programs satisfy H2 pointwise.                        *)
(*                                                                                                *)
(* This is the only place the specific programs of Figure 1 are unfolded, and the only place      *)
(* `RobustMix` is used.  Everything above is generic.                                             *)
(*                                                                                                *)
(**************************************************************************************************)

\* Only StoreBid and ViewItem requests exist under the robust mix.
LEMMA ReqTypes == \A req \in Requests : req.type \in {"StoreBid", "ViewItem"}
  BY RobustMix DEF Requests

\* The program-level form of H2: if a program writes at all, each of its reads is of a key it
\* also writes.
Subsumed(prog) ==
  (\E j \in 1..Len(prog) : prog[j].type = "write") =>
    \A i \in 1..Len(prog) :
      prog[i].type = "read" =>
        \E j \in 1..Len(prog) : prog[j].type = "write" /\ prog[j].key = prog[i].key

(*------------------------------------------------------------------------------------------*)
(* The two enabled programs, unfolded.  Both are short enough to write out literally, which   *)
(* avoids any reasoning about `ConcatOver` / `Flatten` / `SeqOf` -- the machinery that made    *)
(* the corresponding TPC-C step hard.  (RegUser and ViewUsers, which DO use `ConcatOver` to    *)
(* scan the whole USERS domain, are excluded by `RobustMix`.)                                  *)
(*------------------------------------------------------------------------------------------*)
LEMMA StoreBidShape ==
  ASSUME NEW tid, NEW req, req.type = "StoreBid", NEW snap
  PROVE  LET prog == ProgramFor(tid, req, snap) IN
         /\ Len(prog) = 3
         /\ prog[1] = [type |-> "write", key |-> BidKey(tid),     val |-> Tag]
         /\ prog[2] = [type |-> "read",  key |-> ItemKey(req.iid), val |-> snap[ItemKey(req.iid)]]
         /\ prog[3] = [type |-> "write", key |-> ItemKey(req.iid), val |-> snap[ItemKey(req.iid)] + 1]
  BY DEF ProgramFor, StoreBidProgram, Rd, Wr

LEMMA ViewItemShape ==
  ASSUME NEW tid, NEW req, req.type = "ViewItem", NEW snap
  PROVE  LET prog == ProgramFor(tid, req, snap) IN
         /\ Len(prog) = 1
         /\ prog[1] = [type |-> "read", key |-> ItemKey(req.iid), val |-> snap[ItemKey(req.iid)]]
  BY DEF ProgramFor, ViewItemProgram, Rd

(*------------------------------------------------------------------------------------------*)
(* H2, at the level of programs.                                                              *)
(*                                                                                            *)
(* StoreBid: its single read (position 2) is of ITEM(iid), and position 3 writes exactly that  *)
(* key.  The BIDS write at position 1 is never read by anyone, so it is harmless.              *)
(*                                                                                            *)
(* ViewItem: no write at all, so the implication is vacuously true.                            *)
(*------------------------------------------------------------------------------------------*)
THEOREM WorkloadSubsumed ==
  ASSUME NEW tid, NEW req \in Requests, NEW snap
  PROVE  Subsumed(ProgramFor(tid, req, snap))
PROOF
  <1> DEFINE prog == ProgramFor(tid, req, snap)
  <1>1. CASE req.type = "StoreBid"
    <2>1. /\ Len(prog) = 3
          /\ prog[1] = [type |-> "write", key |-> BidKey(tid),     val |-> Tag]
          /\ prog[2] = [type |-> "read",  key |-> ItemKey(req.iid), val |-> snap[ItemKey(req.iid)]]
          /\ prog[3] = [type |-> "write", key |-> ItemKey(req.iid), val |-> snap[ItemKey(req.iid)] + 1]
      BY <1>1, StoreBidShape
    <2>2. QED BY <2>1 DEF Subsumed
  <1>2. CASE req.type = "ViewItem"
    <2>1. /\ Len(prog) = 1
          /\ prog[1] = [type |-> "read", key |-> ItemKey(req.iid), val |-> snap[ItemKey(req.iid)]]
      BY <1>2, ViewItemShape
    <2>2. QED BY <2>1 DEF Subsumed
  <1>3. QED BY <1>1, <1>2, ReqTypes

----------------------------------------------------------------------------------------------------
(**************************************************************************************************)
(*                                                                                                *)
(* Part 5.  Sequence infrastructure.                                                              *)
(*                                                                                                *)
(* Everything the graph is built from reads the history only through `SI!Range`, so the only      *)
(* structural fact needed about `txnHistory` is that it IS a sequence -- of what does not matter.  *)
(* Carrying `\E S : h \in Seq(S)` rather than a precise op type is what keeps the inductive        *)
(* invariant manageable: no reasoning about the value domain of reads and writes is required, and  *)
(* so nothing here depends on `TypeOK`.                                                            *)
(*                                                                                                *)
(**************************************************************************************************)

IsSeq(h) == \E S : h \in Seq(S)

LEMMA EmptyIsSeq == IsSeq(<<>>)
  BY EmptySeq DEF IsSeq

\* Concatenation of two sequences is a sequence, and its range is the union of the ranges.
\* (Stated together because both come from the same `Seq(S1 \cup S2)` widening.)
LEMMA ConcatIsSeq ==
  ASSUME NEW h, NEW b, IsSeq(h), IsSeq(b)
  PROVE  /\ IsSeq(h \o b)
         /\ SI!Range(h \o b) = SI!Range(h) \cup SI!Range(b)
PROOF
  <1>1. PICK S1 : h \in Seq(S1) BY DEF IsSeq
  <1>2. PICK S2 : b \in Seq(S2) BY DEF IsSeq
  <1>3. h \in Seq(S1 \cup S2) /\ b \in Seq(S1 \cup S2)
    BY <1>1, <1>2, SeqMonotonic
  <1>4. (h \o b) \in Seq(S1 \cup S2) BY <1>3, ConcatProperties
  <1>5. Range(h \o b) = Range(h) \cup Range(b) BY <1>3, RangeConcatenation
  <1>6. QED BY <1>4, <1>5 DEF IsSeq, SI!Range, Range

\* A one-element sequence, and its range.
LEMMA SingletonIsSeq ==
  ASSUME NEW o
  PROVE  /\ IsSeq(<<o>>)
         /\ SI!Range(<<o>>) = {o}
PROOF
  <1>1. <<o>> \in Seq({o}) BY IsASeq
  <1>2. QED BY <1>1 DEF IsSeq, SI!Range

\* A function tabulated on 1..n is a sequence, whatever its values.  This is what makes the
\* body block that `StartAndRun` appends a sequence.
LEMMA TabIsSeq ==
  ASSUME NEW n \in Nat, NEW e(_)
  PROVE  IsSeq([i \in 1..n |-> e(i)])
PROOF
  <1> DEFINE S == {e(i) : i \in 1..n}
  <1>1. \A i \in 1..n : e(i) \in S OBVIOUS
  <1>2. [i \in 1..n |-> e(i)] \in Seq(S) BY <1>1, IsASeq
  <1>3. QED BY <1>2 DEF IsSeq

\* `Append` in the spec, as the `\o <<o>>` the lemmas are phrased in.
LEMMA AppendAsConcat ==
  ASSUME NEW h, IsSeq(h), NEW o
  PROVE  Append(h, o) = h \o <<o>>
PROOF
  <1>1. PICK S : h \in Seq(S) BY DEF IsSeq
  <1>2. h \in Seq(S \cup {o}) BY <1>1, SeqMonotonic
  <1>3. o \in S \cup {o} OBVIOUS
  <1>4. QED BY <1>2, <1>3, AppendIsConcat

\* Range of an appended history.
LEMMA RangeAppend ==
  ASSUME NEW h, IsSeq(h), NEW o
  PROVE  /\ IsSeq(Append(h, o))
         /\ SI!Range(Append(h, o)) = SI!Range(h) \cup {o}
PROOF
  <1>1. Append(h, o) = h \o <<o>> BY AppendAsConcat
  <1>2. IsSeq(<<o>>) /\ SI!Range(<<o>>) = {o} BY SingletonIsSeq
  <1>3. QED BY <1>1, <1>2, ConcatIsSeq

----------------------------------------------------------------------------------------------------
(**************************************************************************************************)
(*                                                                                                *)
(* Part 6.  Stability lemmas.                                                                     *)
(*                                                                                                *)
(* Every ingredient of the serialization graph -- `CommittedTxns`, `ReadsByTxn`, `WritesByTxn`,   *)
(* `BeginOp`, `CommitOp` -- is a filter over `SI!Range(h)`.  So all of them are stable under      *)
(* extending the history with ops that the filter rejects.  Stating this over ranges rather than  *)
(* over `Append` handles `StartAndRun`, which appends a begin op plus a whole body in one step.   *)
(*                                                                                                *)
(**************************************************************************************************)

\* Choosing from a set with exactly one witness returns that witness.  Needed because `BeginOp`
\* and `CommitOp` are CHOOSEs over the (growing) range of the history: they are only stable
\* because the op they select is unique.
LEMMA ChooseUnique ==
  ASSUME NEW S, NEW P(_), NEW x \in S, P(x),
         \A y \in S : P(y) => y = x
  PROVE  (CHOOSE y \in S : P(y)) = x
PROOF
  <1>1. \E y \in S : P(y) OBVIOUS
  <1>2. P(CHOOSE y \in S : P(y)) /\ (CHOOSE y \in S : P(y)) \in S BY <1>1
  <1>3. QED BY <1>2

\* Per-transaction data is unchanged by ops belonging to other transactions.
LEMMA StableRange ==
  ASSUME NEW h, NEW hh, NEW t,
         SI!Range(h) \subseteq SI!Range(hh),
         \A o \in SI!Range(hh) \ SI!Range(h) : o.txnId # t
  PROVE  /\ SI!ReadsByTxn(hh, t)  = SI!ReadsByTxn(h, t)
         /\ SI!WritesByTxn(hh, t) = SI!WritesByTxn(h, t)
         /\ SI!BeginOp(hh, t)     = SI!BeginOp(h, t)
         /\ SI!CommitOp(hh, t)    = SI!CommitOp(h, t)
PROOF
  <1>1. \A x : (x \in SI!Range(hh) /\ x.txnId = t) <=> (x \in SI!Range(h) /\ x.txnId = t)
    OBVIOUS
  <1>2. {op \in SI!Range(hh) : op.txnId = t /\ op.type = "read"}
        = {op \in SI!Range(h) : op.txnId = t /\ op.type = "read"}
    BY <1>1
  <1>3. {op \in SI!Range(hh) : op.txnId = t /\ op.type = "write"}
        = {op \in SI!Range(h) : op.txnId = t /\ op.type = "write"}
    BY <1>1
  <1>4. \A x : (x \in SI!Range(hh) /\ (x.txnId = t /\ x.type = "begin"))
            <=> (x \in SI!Range(h) /\ (x.txnId = t /\ x.type = "begin"))
    BY <1>1
  <1>5. \A x : (x \in SI!Range(hh) /\ (x.txnId = t /\ x.type = "commit"))
            <=> (x \in SI!Range(h) /\ (x.txnId = t /\ x.type = "commit"))
    BY <1>1
  <1>6. QED BY <1>2, <1>3, <1>4, <1>5
        DEF SI!ReadsByTxn, SI!WritesByTxn, SI!BeginOp, SI!CommitOp

\* The committed set is unchanged by non-commit ops.
LEMMA CommittedStable ==
  ASSUME NEW h, NEW hh,
         SI!Range(h) \subseteq SI!Range(hh),
         \A o \in SI!Range(hh) \ SI!Range(h) : o.type # "commit"
  PROVE  SI!CommittedTxns(hh) = SI!CommittedTxns(h)
PROOF
  <1>1. {x \in SI!Range(hh) : x.type = "commit"} = {x \in SI!Range(h) : x.type = "commit"}
    OBVIOUS
  <1>2. QED BY <1>1 DEF SI!CommittedTxns

\* Appending a commit op adds exactly its transaction to the committed set.
LEMMA CommittedAdd ==
  ASSUME NEW h, IsSeq(h), NEW o, o.type = "commit"
  PROVE  SI!CommittedTxns(Append(h, o)) = SI!CommittedTxns(h) \cup {o.txnId}
PROOF
  <1>1. SI!Range(Append(h, o)) = SI!Range(h) \cup {o} BY RangeAppend
  <1>2. {x \in SI!Range(Append(h, o)) : x.type = "commit"}
        = {x \in SI!Range(h) : x.type = "commit"} \cup {o}
    BY <1>1
  <1>3. QED BY <1>2 DEF SI!CommittedTxns

----------------------------------------------------------------------------------------------------
(**************************************************************************************************)
(*                                                                                                *)
(* Part 7.  The body block appended by `StartAndRun`.                                             *)
(*                                                                                                *)
(* `StartAndRun` appends `<<beginOp>> \o events`, where `events` re-tags each program op with the  *)
(* transaction id.  This part computes the range of that block for each enabled request type and   *)
(* reads H2 off it.  Because the two enabled programs have length 3 and 1, their ops can be        *)
(* enumerated literally, so none of `ConcatOver` / `Flatten` / `SeqOf` has to be reasoned about.    *)
(*                                                                                                *)
(**************************************************************************************************)

\* Re-tagging a program op with a txnId, computed.
LEMMA MergeOp ==
  ASSUME NEW ty, NEW k, NEW v, NEW tid
  PROVE  [type |-> ty, key |-> k, val |-> v] @@ [txnId |-> tid]
         = [type |-> ty, key |-> k, val |-> v, txnId |-> tid]
  OBVIOUS

\* A function whose domain is 1..n is a sequence, with the range you would expect.  Specialized
\* to n = 3 and n = 1, the two program lengths in the robust mix, because the general
\* higher-order form does not instantiate cleanly against a local DEFINE in tlapm 1.5.0.
LEMMA Fcn3IsSeqRange ==
  ASSUME NEW a, NEW b, NEW c, NEW f, f = [i \in 1..3 |-> IF i = 1 THEN a ELSE IF i = 2 THEN b ELSE c]
  PROVE  IsSeq(f) /\ SI!Range(f) = {a, b, c}
PROOF
  <1> DEFINE S == {a, b, c}
  <1>1. f \in [1..3 -> S] BY DEF S
  <1>2. f \in Seq(S) BY <1>1, SeqDef
  <1>3. SI!Range(f) = {f[i] : i \in 1..3} BY <1>1 DEF SI!Range
  <1>4. {f[i] : i \in 1..3} = {a, b, c} OBVIOUS
  <1>5. QED BY <1>2, <1>3, <1>4 DEF IsSeq

LEMMA Fcn1IsSeqRange ==
  ASSUME NEW a, NEW f, f = [i \in 1..1 |-> a]
  PROVE  IsSeq(f) /\ SI!Range(f) = {a}
PROOF
  <1> DEFINE S == {a}
  <1>1. f \in [1..1 -> S] BY DEF S
  <1>2. f \in Seq(S) BY <1>1, SeqDef
  <1>3. SI!Range(f) = {f[i] : i \in 1..1} BY <1>1 DEF SI!Range
  <1>4. {f[i] : i \in 1..1} = {a} OBVIOUS
  <1>5. QED BY <1>2, <1>3, <1>4 DEF IsSeq


(*------------------------------------------------------------------------------------------*)
(* The body block: it is a sequence, every op in it belongs to `tid` and is a read or write,  *)
(* and its reads are subsumed by its writes (H2, at the level of one transaction's body).     *)
(*------------------------------------------------------------------------------------------*)
LEMMA BodyOps ==
  ASSUME NEW tid, NEW req \in Requests, NEW snap,
         NEW events,
         events = [i \in 1..Len(ProgramFor(tid, req, snap)) |->
                      ProgramFor(tid, req, snap)[i] @@ [txnId |-> tid]]
  PROVE  /\ IsSeq(events)
         /\ \A o \in SI!Range(events) : o.txnId = tid /\ o.type \in {"read", "write"}
         /\ LET W == {o \in SI!Range(events) : o.type = "write"}
                R == {o \in SI!Range(events) : o.type = "read"}
            IN W # {} => \A r \in R : \E w \in W : w.key = r.key
PROOF
  <1> DEFINE prog == ProgramFor(tid, req, snap)
             tag(i) == prog[i] @@ [txnId |-> tid]
             W == {o \in SI!Range(events) : o.type = "write"}
             R == {o \in SI!Range(events) : o.type = "read"}
  \* StoreBid: one read of ITEM(iid), writes of BID(tid) and ITEM(iid).  The read's key is
  \* written by the third op, which is what H2 asks for.
  <1>1. CASE req.type = "StoreBid"
    <2>1. /\ Len(prog) = 3
          /\ prog[1] = [type |-> "write", key |-> BidKey(tid),      val |-> Tag]
          /\ prog[2] = [type |-> "read",  key |-> ItemKey(req.iid), val |-> snap[ItemKey(req.iid)]]
          /\ prog[3] = [type |-> "write", key |-> ItemKey(req.iid), val |-> snap[ItemKey(req.iid)] + 1]
      BY <1>1, StoreBidShape
    <2>2. IsSeq(events) /\ SI!Range(events) = {tag(1), tag(2), tag(3)}
      <3>1. events = [i \in 1..3 |->
                        IF i = 1 THEN tag(1) ELSE IF i = 2 THEN tag(2) ELSE tag(3)]
        BY <2>1
      <3>2. QED BY <3>1, Fcn3IsSeqRange
    <2>3. /\ tag(1) = [type |-> "write", key |-> BidKey(tid), val |-> Tag, txnId |-> tid]
          /\ tag(2) = [type |-> "read", key |-> ItemKey(req.iid),
                       val |-> snap[ItemKey(req.iid)], txnId |-> tid]
          /\ tag(3) = [type |-> "write", key |-> ItemKey(req.iid),
                       val |-> snap[ItemKey(req.iid)] + 1, txnId |-> tid]
      BY <2>1, MergeOp
    <2>5. \A o \in SI!Range(events) : o.txnId = tid /\ o.type \in {"read", "write"}
      BY <2>2, <2>3
    <2>6. W # {} => \A r \in R : \E w \in W : w.key = r.key
      <3>1. R = {tag(2)} BY <2>2, <2>3
      <3>2. tag(3) \in W BY <2>2, <2>3
      <3>3. tag(3).key = tag(2).key BY <2>3
      <3>4. QED BY <3>1, <3>2, <3>3
    <2>7. QED BY <2>2, <2>5, <2>6
  \* ViewItem: read-only, so the H2 obligation is vacuous.
  <1>2. CASE req.type = "ViewItem"
    <2>1. /\ Len(prog) = 1
          /\ prog[1] = [type |-> "read", key |-> ItemKey(req.iid), val |-> snap[ItemKey(req.iid)]]
      BY <1>2, ViewItemShape
    <2>2. IsSeq(events) /\ SI!Range(events) = {tag(1)}
      <3>1. events = [i \in 1..1 |-> tag(1)] BY <2>1
      <3>2. QED BY <3>1, Fcn1IsSeqRange
    <2>3. tag(1) = [type |-> "read", key |-> ItemKey(req.iid),
                    val |-> snap[ItemKey(req.iid)], txnId |-> tid]
      BY <2>1, MergeOp
    <2>5. \A o \in SI!Range(events) : o.txnId = tid /\ o.type \in {"read", "write"}
      BY <2>2, <2>3
    <2>6. W = {} BY <2>2, <2>3
    <2>7. QED BY <2>2, <2>5, <2>6
  <1>3. QED BY <1>1, <1>2, ReqTypes

----------------------------------------------------------------------------------------------------
(**************************************************************************************************)
(*                                                                                                *)
(* Part 8.  The inductive invariant.                                                              *)
(*                                                                                                *)
(* `HistoryOK` is not by itself inductive: H1 and H3 are statements about begin and commit times,  *)
(* and re-establishing them at a commit step needs to know how those times relate to the clock and *)
(* to `runningTxns`.  So the invariant carries the supporting facts explicitly.                    *)
(*                                                                                                *)
(* The clauses are stated over `Ops`, the range of the history, rather than over `SI!BeginOp` /    *)
(* `SI!CommitOp`.  Those two are CHOOSEs, and reasoning about a CHOOSE over a growing set needs    *)
(* uniqueness at every step; quantifying over ops instead and converting once, at the very end     *)
(* (`InvImpliesHistoryOK`), keeps the uniqueness reasoning in one place.                          *)
(*                                                                                                *)
(**************************************************************************************************)

Ops == SI!Range(txnHistory)

\* Timestamped ops -- the ones that carry a `time` field.
Stamped(o) == o.type \in {"begin", "commit", "abort"}

\* The keys a transaction writes, as read off the history.
WKeys(t) == {w.key : w \in SI!WritesByTxn(txnHistory, t)}

(*------------------------------------------------------------------------------------------*)
(* Structural clauses.                                                                        *)
(*------------------------------------------------------------------------------------------*)

\* The history is a sequence (needed to compute the range of an extension at all).
InvSeq == IsSeq(txnHistory)

\* The clock is a natural, and no event in the history is stamped later than it.  This is the
\* clock-monotonicity fact both H1 and H3 rest on.
InvClock == /\ clock \in Nat
            /\ \A o \in Ops : Stamped(o) => (o.time \in Nat /\ o.time =< clock)

\* A transaction begins at most once and commits at most once.  This is what makes `SI!BeginOp`
\* and `SI!CommitOp` well defined, i.e. what lets the CHOOSEs be pinned down.
InvUnique ==
  /\ \A o1, o2 \in Ops :
        (o1.type = "begin" /\ o2.type = "begin" /\ o1.txnId = o2.txnId) => o1 = o2
  /\ \A o1, o2 \in Ops :
        (o1.type = "commit" /\ o2.type = "commit" /\ o1.txnId = o2.txnId) => o1 = o2

\* A commit op records exactly the keys its transaction wrote.  (Needed because H3 is read off
\* `updatedKeys` in the First-Committer-Wins test, but stated in terms of write ops.)
InvCommitKeys ==
  \A o \in Ops : o.type = "commit" => o.updatedKeys = WKeys(o.txnId)

\* Every running transaction has a matching begin op, started no later than now, and has not
\* already committed.  The last clause is what makes the committing transaction a genuinely new
\* node: without it, nothing rules out a second commit op for an id that already has one.
InvRunning ==
  \A r \in runningTxns :
    /\ r.startTime \in Nat
    /\ r.startTime =< clock
    /\ \E b \in Ops : b.type = "begin" /\ b.txnId = r.id /\ b.time = r.startTime
    /\ \A x \in Ops : x.type = "commit" => x.txnId # r.id

(*------------------------------------------------------------------------------------------*)
(* The three history properties, in ops form.                                                 *)
(*------------------------------------------------------------------------------------------*)

\* H1: every commit is preceded by the transaction's own begin.
InvH1 ==
  \A o \in Ops :
    o.type = "commit" =>
      \E b \in Ops : b.type = "begin" /\ b.txnId = o.txnId /\ b.time < o.time

\* H2: a transaction that writes reads only keys it writes.  This is the workload clause, and
\* the only one whose proof looks at what the programs actually do.
InvH2 ==
  \A t : SI!WritesByTxn(txnHistory, t) # {} =>
           \A rd \in SI!ReadsByTxn(txnHistory, t) : rd.key \in WKeys(t)

\* H3: First-Committer-Wins.  Two distinct committed transactions writing a common key are
\* separated: one commits no later than the other begins.
InvH3 ==
  \A o1, o2 \in Ops :
    (/\ o1.type = "commit" /\ o2.type = "commit"
     /\ o1.txnId # o2.txnId
     /\ WKeys(o1.txnId) \cap WKeys(o2.txnId) # {}) =>
       \/ \E b2 \in Ops : b2.type = "begin" /\ b2.txnId = o2.txnId /\ o1.time =< b2.time
       \/ \E b1 \in Ops : b1.type = "begin" /\ b1.txnId = o1.txnId /\ o2.time =< b1.time

Inv == /\ InvSeq
       /\ InvClock
       /\ InvUnique
       /\ InvCommitKeys
       /\ InvRunning
       /\ InvH1
       /\ InvH2
       /\ InvH3

----------------------------------------------------------------------------------------------------
(**************************************************************************************************)
(*                                                                                                *)
(* Part 9.  From `Inv` to `HistoryOK`.                                                            *)
(*                                                                                                *)
(* This converts the ops-form clauses into the `SI!BeginOp` / `SI!CommitOp` form that Part 3       *)
(* speaks, which is where `InvUnique` is used: a CHOOSE picks the unique begin (resp. commit) op   *)
(* of a transaction exactly when there is only one.                                               *)
(*                                                                                                *)
(**************************************************************************************************)

\* The commit op of a committed transaction is the op that put it in the committed set.
LEMMA CommitOpIs ==
  ASSUME InvUnique, NEW o \in Ops, o.type = "commit"
  PROVE  SI!CommitOp(txnHistory, o.txnId) = o
PROOF
  <1> DEFINE P(x) == x.txnId = o.txnId /\ x.type = "commit"
  <1>1. P(o) OBVIOUS
  <1>2. \A y \in Ops : P(y) => y = o BY DEF InvUnique
  <1>3. (CHOOSE y \in Ops : P(y)) = o BY <1>1, <1>2, ChooseUnique
  <1>4. QED BY <1>3 DEF SI!CommitOp, Ops

\* Likewise for begin ops.
LEMMA BeginOpIs ==
  ASSUME InvUnique, NEW b \in Ops, b.type = "begin"
  PROVE  SI!BeginOp(txnHistory, b.txnId) = b
PROOF
  <1> DEFINE P(x) == x.txnId = b.txnId /\ x.type = "begin"
  <1>1. P(b) OBVIOUS
  <1>2. \A y \in Ops : P(y) => y = b BY DEF InvUnique
  <1>3. (CHOOSE y \in Ops : P(y)) = b BY <1>1, <1>2, ChooseUnique
  <1>4. QED BY <1>3 DEF SI!BeginOp, Ops

\* A committed transaction has a commit op in the history.
LEMMA CommittedHasOp ==
  ASSUME NEW t \in SI!CommittedTxns(txnHistory)
  PROVE  \E o \in Ops : o.type = "commit" /\ o.txnId = t
  BY DEF SI!CommittedTxns, Ops

(*------------------------------------------------------------------------------------------*)
(* `WKeys` is the key set of the write ops, which is how H2 and H3 connect to `SI!Writes`.    *)
(*------------------------------------------------------------------------------------------*)
LEMMA WKeysShared ==
  ASSUME NEW t1, NEW t2,
         \E w1 \in SI!WritesByTxn(txnHistory, t1), w2 \in SI!WritesByTxn(txnHistory, t2) :
            w1.key = w2.key
  PROVE  WKeys(t1) \cap WKeys(t2) # {}
  BY DEF WKeys

(*------------------------------------------------------------------------------------------*)
(* The conversion itself.                                                                     *)
(*------------------------------------------------------------------------------------------*)
THEOREM InvImpliesHistoryOK == Inv => HistoryOK(txnHistory)
PROOF
  <1> SUFFICES ASSUME Inv PROVE HistoryOK(txnHistory) OBVIOUS
  <1>u. InvUnique BY DEF Inv
  \* H1.  The commit op is `o`; the begin op is the `b` supplied by InvH1; both times are
  \* naturals by InvClock, and b.time < o.time is exactly what InvH1 gives.
  <1>1. LifetimeOK(txnHistory)
    <2>1. SUFFICES ASSUME NEW t \in SI!CommittedTxns(txnHistory)
                   PROVE  /\ Begin(txnHistory, t)  \in Nat
                          /\ Commit(txnHistory, t) \in Nat
                          /\ Begin(txnHistory, t) < Commit(txnHistory, t)
      BY DEF LifetimeOK
    <2>2. PICK o \in Ops : o.type = "commit" /\ o.txnId = t BY <2>1, CommittedHasOp
    <2>3. SI!CommitOp(txnHistory, t) = o BY <2>2, <1>u, CommitOpIs
    <2>4. PICK b \in Ops : b.type = "begin" /\ b.txnId = t /\ b.time < o.time
      BY <2>2 DEF Inv, InvH1
    <2>5. SI!BeginOp(txnHistory, t) = b BY <2>4, <1>u, BeginOpIs
    <2>6. o.time \in Nat /\ b.time \in Nat
      BY <2>2, <2>4 DEF Inv, InvClock, Stamped
    <2>7. QED BY <2>3, <2>4, <2>5, <2>6 DEF Begin, Commit
  \* H2.  Direct from InvH2, modulo unfolding WKeys.
  <1>2. ReadsSubsumed(txnHistory)
    <2>1. SUFFICES ASSUME NEW t \in SI!CommittedTxns(txnHistory),
                          Updater(txnHistory, t),
                          NEW rop \in SI!ReadsByTxn(txnHistory, t)
                   PROVE  \E wop \in SI!WritesByTxn(txnHistory, t) : wop.key = rop.key
      BY DEF ReadsSubsumed
    <2>2. SI!WritesByTxn(txnHistory, t) # {} BY <2>1 DEF Updater
    <2>3. rop.key \in WKeys(t) BY <2>2, <2>1 DEF Inv, InvH2
    <2>4. QED BY <2>3 DEF WKeys
  \* H3.  The two commit ops are the CommitOps; InvH3 supplies a begin op on one side or the
  \* other, and BeginOpIs identifies it with the BeginOp.
  <1>3. FCWDisjoint(txnHistory)
    <2>1. SUFFICES ASSUME NEW t1 \in SI!CommittedTxns(txnHistory),
                          NEW t2 \in SI!CommittedTxns(txnHistory),
                          t1 # t2,
                          \E w1 \in SI!WritesByTxn(txnHistory, t1),
                             w2 \in SI!WritesByTxn(txnHistory, t2) : w1.key = w2.key
                   PROVE  \/ Commit(txnHistory, t1) =< Begin(txnHistory, t2)
                          \/ Commit(txnHistory, t2) =< Begin(txnHistory, t1)
      BY DEF FCWDisjoint
    <2>2. PICK o1 \in Ops : o1.type = "commit" /\ o1.txnId = t1 BY <2>1, CommittedHasOp
    <2>3. PICK o2 \in Ops : o2.type = "commit" /\ o2.txnId = t2 BY <2>1, CommittedHasOp
    <2>4. SI!CommitOp(txnHistory, t1) = o1 /\ SI!CommitOp(txnHistory, t2) = o2
      BY <2>2, <2>3, <1>u, CommitOpIs
    <2>5. WKeys(t1) \cap WKeys(t2) # {} BY <2>1, WKeysShared
    <2>6. \/ \E b2 \in Ops : b2.type = "begin" /\ b2.txnId = t2 /\ o1.time =< b2.time
          \/ \E b1 \in Ops : b1.type = "begin" /\ b1.txnId = t1 /\ o2.time =< b1.time
      BY <2>2, <2>3, <2>5, <2>1 DEF Inv, InvH3
    <2>7. CASE \E b2 \in Ops : b2.type = "begin" /\ b2.txnId = t2 /\ o1.time =< b2.time
      <3>1. PICK b2 \in Ops : b2.type = "begin" /\ b2.txnId = t2 /\ o1.time =< b2.time BY <2>7
      <3>2. SI!BeginOp(txnHistory, t2) = b2 BY <3>1, <1>u, BeginOpIs
      <3>3. QED BY <3>1, <3>2, <2>4 DEF Begin, Commit
    <2>8. CASE \E b1 \in Ops : b1.type = "begin" /\ b1.txnId = t1 /\ o2.time =< b1.time
      <3>1. PICK b1 \in Ops : b1.type = "begin" /\ b1.txnId = t1 /\ o2.time =< b1.time BY <2>8
      <3>2. SI!BeginOp(txnHistory, t1) = b1 BY <3>1, <1>u, BeginOpIs
      <3>3. QED BY <3>1, <3>2, <2>4 DEF Begin, Commit
    <2>9. QED BY <2>6, <2>7, <2>8
  <1>4. QED BY <1>1, <1>2, <1>3 DEF HistoryOK

\* Hence the invariant implies the property we are after.
THEOREM InvImpliesSerializable == Inv => SerializableViaPath
PROOF
  <1>1. Inv => HistoryOK(txnHistory) BY InvImpliesHistoryOK
  <1>2. QED BY <1>1, HistoryOKImpliesSerializable
        DEF SerializableViaPath

----------------------------------------------------------------------------------------------------
(**************************************************************************************************)
(*                                                                                                *)
(* Part 10.  `Inv` holds initially.                                                               *)
(*                                                                                                *)
(**************************************************************************************************)

THEOREM InitInv == Init => Inv
PROOF
  <1> SUFFICES ASSUME Init PROVE Inv OBVIOUS
  <1>1. txnHistory = <<>> /\ clock = 0 /\ runningTxns = {} BY DEF Init
  <1>2. Ops = {} BY <1>1, EmptyRange DEF Ops
  <1>3. InvSeq BY <1>1, EmptyIsSeq DEF InvSeq
  <1>4. InvClock BY <1>1, <1>2 DEF InvClock
  <1>5. InvUnique BY <1>2 DEF InvUnique
  <1>6. InvCommitKeys BY <1>2 DEF InvCommitKeys
  <1>7. InvRunning BY <1>1 DEF InvRunning
  <1>8. InvH1 BY <1>2 DEF InvH1
  \* No ops at all, so in particular no write ops, and H2's hypothesis is unsatisfiable.
  <1>9. InvH2
    <2>1. \A t : SI!WritesByTxn(txnHistory, t) = {} BY <1>2 DEF SI!WritesByTxn, Ops
    <2>2. QED BY <2>1 DEF InvH2
  <1>10. InvH3 BY <1>2 DEF InvH3
  <1>11. QED BY <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10 DEF Inv

----------------------------------------------------------------------------------------------------
(**************************************************************************************************)
(*                                                                                                *)
(* Part 11.  The abort step.                                                                      *)
(*                                                                                                *)
(* An abort appends one op that is neither a begin nor a commit and carries no keys.  So every    *)
(* clause is preserved almost by inspection: the only op-quantified clauses that could notice it  *)
(* are `InvClock` (its time is clock+1, which is the new clock) and the structural ones, which     *)
(* reject it on its type.  Reads and writes are untouched, so H2 is verbatim.                     *)
(*                                                                                                *)
(**************************************************************************************************)

\* Common shape of an appended-op step: how `Ops` and the per-transaction read/write sets move.
LEMMA OpsAppend ==
  ASSUME InvSeq, NEW o, txnHistory' = Append(txnHistory, o)
  PROVE  /\ IsSeq(txnHistory')
         /\ Ops' = Ops \cup {o}
PROOF
  <1>1. IsSeq(txnHistory) BY DEF InvSeq
  <1>2. QED BY <1>1, RangeAppend DEF Ops

\* Appending a non-read/non-write op leaves all read and write sets alone.
LEMMA RWUnchangedAppend ==
  ASSUME NEW o, o.type \notin {"read", "write"}, Ops' = Ops \cup {o}
  PROVE  /\ \A t : SI!WritesByTxn(txnHistory', t) = SI!WritesByTxn(txnHistory, t)
         /\ \A t : SI!ReadsByTxn(txnHistory', t)  = SI!ReadsByTxn(txnHistory, t)
         /\ \A t : WKeys(t)' = WKeys(t)
PROOF
  <1>1. \A t : {x \in Ops' : x.txnId = t /\ x.type = "write"}
             = {x \in Ops  : x.txnId = t /\ x.type = "write"}
    OBVIOUS
  <1>2. \A t : {x \in Ops' : x.txnId = t /\ x.type = "read"}
             = {x \in Ops  : x.txnId = t /\ x.type = "read"}
    OBVIOUS
  <1>3. QED BY <1>1, <1>2 DEF SI!WritesByTxn, SI!ReadsByTxn, WKeys, Ops

THEOREM StepAbort ==
  ASSUME Inv, NEW tid \in TxnIds, AbortTxn(tid)
  PROVE  Inv'
PROOF
  <1> DEFINE o == [type |-> "abort", txnId |-> tid, time |-> clock + 1]
  <1>1. /\ txnHistory' = Append(txnHistory, o)
        /\ clock' = clock + 1
        /\ runningTxns' = {r \in runningTxns : r.id # tid}
    BY DEF AbortTxn, SI!AbortTxn
  <1>2. IsSeq(txnHistory') /\ Ops' = Ops \cup {o}
    BY <1>1, OpsAppend DEF Inv, InvSeq
  <1>3. /\ \A t : SI!WritesByTxn(txnHistory', t) = SI!WritesByTxn(txnHistory, t)
        /\ \A t : SI!ReadsByTxn(txnHistory', t)  = SI!ReadsByTxn(txnHistory, t)
        /\ \A t : WKeys(t)' = WKeys(t)
    BY <1>2, RWUnchangedAppend
  <1>4. InvSeq' BY <1>2 DEF InvSeq
  \* The new op is stamped at the new clock; every old op was =< the old clock, hence =< the new.
  <1>5. InvClock'
    <2>1. clock' \in Nat BY <1>1 DEF Inv, InvClock
    <2>2. \A x \in Ops : Stamped(x) => (x.time \in Nat /\ x.time =< clock')
      BY <1>1 DEF Inv, InvClock
    <2>3. o.time \in Nat /\ o.time =< clock' BY <1>1 DEF Inv, InvClock
    <2>4. QED BY <1>2, <2>1, <2>2, <2>3 DEF InvClock
  \* An abort op is neither a begin nor a commit, so the uniqueness clauses do not see it.
  <1>6. InvUnique' BY <1>2 DEF Inv, InvUnique
  <1>7. InvCommitKeys' BY <1>2, <1>3 DEF Inv, InvCommitKeys
  \* The aborting transaction leaves the running set; the others keep their begin ops, which
  \* are still in the (larger) history.
  <1>8. InvRunning'
    <2>1. SUFFICES ASSUME NEW r \in runningTxns'
                   PROVE  /\ r.startTime \in Nat
                          /\ r.startTime =< clock'
                          /\ \E b \in Ops' : b.type = "begin" /\ b.txnId = r.id
                                             /\ b.time = r.startTime
                          /\ \A x \in Ops' : x.type = "commit" => x.txnId # r.id
      BY DEF InvRunning
    <2>2. r \in runningTxns BY <1>1
    <2>3. /\ r.startTime \in Nat
          /\ r.startTime =< clock
          /\ \E b \in Ops : b.type = "begin" /\ b.txnId = r.id /\ b.time = r.startTime
          /\ \A x \in Ops : x.type = "commit" => x.txnId # r.id
      BY <2>2 DEF Inv, InvRunning
    <2>4. clock \in Nat BY DEF Inv, InvClock
    \* The only new op is an abort op, so no new commit op names anyone.
    <2>5. \A x \in Ops' : x.type = "commit" => x \in Ops BY <1>2
    <2>6. QED BY <2>3, <2>4, <2>5, <1>1, <1>2
  <1>9. InvH1' BY <1>2 DEF Inv, InvH1
  <1>10. InvH2' BY <1>3 DEF Inv, InvH2
  <1>11. InvH3' BY <1>2, <1>3 DEF Inv, InvH3
  <1>12. QED BY <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11 DEF Inv

----------------------------------------------------------------------------------------------------
(**************************************************************************************************)
(*                                                                                                *)
(* Part 12.  The start step.                                                                      *)
(*                                                                                                *)
(* `StartAndRun(tid, req)` appends `<<beginOp>> \o events` in one step: the begin op plus the      *)
(* whole transaction body.  The block contains no commit op, and every op in it carries `tid`,     *)
(* which by the `Unused(tid)` guard appears nowhere in the old history.  That freshness is what    *)
(* keeps the structural clauses true, and `BodyOps` supplies H2 for the new transaction.           *)
(*                                                                                                *)
(**************************************************************************************************)

\* `Unused` says no op in the history mentions the id, which is the freshness the step needs.
LEMMA UnusedMeans ==
  ASSUME NEW tid, Unused(tid)
  PROVE  \A x \in Ops : x.txnId # tid
  BY DEF Unused, Ops

THEOREM StepStart ==
  ASSUME Inv, NEW tid \in TxnIds, NEW req \in Requests, StartAndRun(tid, req)
  PROVE  Inv'
PROOF
  <1> DEFINE prog    == ProgramFor(tid, req, dataStore)
             beginOp == [type |-> "begin", txnId |-> tid, time |-> clock + 1]
             events  == [i \in 1..Len(prog) |-> prog[i] @@ [txnId |-> tid]]
             blk     == <<beginOp>> \o events
  <1>1. /\ Unused(tid)
        /\ txnHistory' = txnHistory \o <<beginOp>> \o events
        /\ clock' = clock + 1
        /\ runningTxns' = runningTxns \cup
                          {[id |-> tid, startTime |-> clock + 1, commitTime |-> Empty]}
    BY DEF StartAndRun
  \* The block, and the range of the extended history.
  <1>2. /\ IsSeq(events)
        /\ \A o \in SI!Range(events) : o.txnId = tid /\ o.type \in {"read", "write"}
        /\ LET W == {o \in SI!Range(events) : o.type = "write"}
               R == {o \in SI!Range(events) : o.type = "read"}
           IN W # {} => \A r \in R : \E w \in W : w.key = r.key
    BY BodyOps
  <1>3. IsSeq(<<beginOp>>) /\ SI!Range(<<beginOp>>) = {beginOp} BY SingletonIsSeq
  <1>4. IsSeq(blk) /\ SI!Range(blk) = {beginOp} \cup SI!Range(events)
    BY <1>2, <1>3, ConcatIsSeq
  <1>5. /\ IsSeq(txnHistory')
        /\ Ops' = Ops \cup SI!Range(blk)
        /\ Ops \subseteq Ops'
    <2>1. IsSeq(txnHistory) BY DEF Inv, InvSeq
    <2>2. txnHistory' = txnHistory \o blk
      BY <1>1, ConcatAssociative, <1>2, <1>3, <2>1 DEF IsSeq
    <2>3. QED BY <2>1, <2>2, <1>4, ConcatIsSeq DEF Ops
  \* The begin op's fields, spelled out: the prover will not read them off the record literal
  \* on its own once `beginOp` is buried inside a set expression.
  <1>5a. /\ beginOp.type  = "begin"
         /\ beginOp.txnId = tid
         /\ beginOp.time  = clock + 1
    OBVIOUS
  <1>5b. Ops' = Ops \cup ({beginOp} \cup SI!Range(events)) BY <1>5, <1>4
  \* Every new op carries `tid`, which is fresh.
  <1>6. \A x \in Ops' \ Ops : x.txnId = tid
    BY <1>5b, <1>5a, <1>2
  <1>7. \A x \in Ops : x.txnId # tid BY <1>1, UnusedMeans
  \* No commit op is added: the block is a begin op plus reads and writes.
  <1>8. \A x \in Ops' \ Ops : x.type # "commit"
    BY <1>5b, <1>5a, <1>2
  <1>9. InvSeq' BY <1>5 DEF InvSeq
  \* Only the begin op is stamped, at the new clock.
  <1>10. InvClock'
    <2>1. clock' \in Nat BY <1>1 DEF Inv, InvClock
    <2>2. \A x \in Ops : Stamped(x) => (x.time \in Nat /\ x.time =< clock')
      BY <1>1 DEF Inv, InvClock
    <2>3. \A x \in SI!Range(events) : ~Stamped(x) BY <1>2 DEF Stamped
    <2>4. beginOp.time \in Nat /\ beginOp.time =< clock' BY <1>1 DEF Inv, InvClock
    <2>5. QED BY <1>5, <1>4, <2>1, <2>2, <2>3, <2>4 DEF InvClock
  \* The one new begin op is for a fresh id, so it collides with nothing; no new commit op.
  <1>11. InvUnique'
    <2>1. SUFFICES ASSUME NEW o1 \in Ops', NEW o2 \in Ops'
                   PROVE  /\ (o1.type = "begin" /\ o2.type = "begin" /\ o1.txnId = o2.txnId)
                             => o1 = o2
                          /\ (o1.type = "commit" /\ o2.type = "commit" /\ o1.txnId = o2.txnId)
                             => o1 = o2
      BY DEF InvUnique
    \* The only new begin op is `beginOp`; any old op has a different txnId.
    <2>2. \A x \in Ops' : x.type = "begin" => (x \in Ops \/ x = beginOp)
      BY <1>5b, <1>2
    <2>3. \A x \in Ops' : x.type = "commit" => x \in Ops BY <1>5, <1>8
    <2>4. QED BY <2>2, <2>3, <1>7 DEF Inv, InvUnique
  \* No new commit op, and no old transaction's write set changes (all new ops carry `tid`,
  \* which no commit op names).
  <1>12. \A t : t # tid => WKeys(t)' = WKeys(t)
    <2>1. SUFFICES ASSUME NEW t, t # tid PROVE WKeys(t)' = WKeys(t) OBVIOUS
    <2>2. {x \in Ops' : x.txnId = t /\ x.type = "write"}
        = {x \in Ops  : x.txnId = t /\ x.type = "write"}
      BY <1>5, <1>6, <2>1
    <2>3. QED BY <2>2 DEF WKeys, SI!WritesByTxn, Ops
  <1>13. InvCommitKeys'
    <2>1. SUFFICES ASSUME NEW o \in Ops', o.type = "commit"
                   PROVE  o.updatedKeys = WKeys(o.txnId)'
      BY DEF InvCommitKeys
    <2>2. o \in Ops BY <2>1, <1>5, <1>8
    <2>3. o.txnId # tid BY <2>2, <1>7
    <2>4. o.updatedKeys = WKeys(o.txnId) BY <2>1, <2>2 DEF Inv, InvCommitKeys
    <2>5. QED BY <2>3, <2>4, <1>12
  \* The new running transaction has `beginOp` as its begin op; the old ones keep theirs.
  <1>14. InvRunning'
    <2>1. SUFFICES ASSUME NEW r \in runningTxns'
                   PROVE  /\ r.startTime \in Nat
                          /\ r.startTime =< clock'
                          /\ \E b \in Ops' : b.type = "begin" /\ b.txnId = r.id
                                             /\ b.time = r.startTime
                          /\ \A x \in Ops' : x.type = "commit" => x.txnId # r.id
      BY DEF InvRunning
    <2>2. clock \in Nat BY DEF Inv, InvClock
    \* No commit op is added, so the "has not committed" clause only has to look at old ops.
    <2>0. \A x \in Ops' : x.type = "commit" => x \in Ops BY <1>5, <1>8
    <2>3. CASE r = [id |-> tid, startTime |-> clock + 1, commitTime |-> Empty]
      <3>1. beginOp \in Ops' BY <1>5b
      <3>2. r.id = tid /\ r.startTime = clock + 1 BY <2>3
      <3>3. r.startTime \in Nat /\ r.startTime =< clock' BY <3>2, <2>2, <1>1
      <3>4. beginOp.type = "begin" /\ beginOp.txnId = r.id /\ beginOp.time = r.startTime
        BY <1>5a, <3>2
      \* `tid` is fresh, so no op at all -- commit or otherwise -- already names it.
      <3>5. \A x \in Ops' : x.type = "commit" => x.txnId # r.id
        BY <2>0, <1>7, <3>2
      <3>6. QED BY <3>1, <3>3, <3>4, <3>5
    <2>4. CASE r \in runningTxns
      <3>1. /\ r.startTime \in Nat
            /\ r.startTime =< clock
            /\ \E b \in Ops : b.type = "begin" /\ b.txnId = r.id /\ b.time = r.startTime
            /\ \A x \in Ops : x.type = "commit" => x.txnId # r.id
        BY <2>4 DEF Inv, InvRunning
      <3>2. QED BY <3>1, <2>2, <2>0, <1>1, <1>5
    <2>5. QED BY <2>1, <2>3, <2>4, <1>1
  <1>15. InvH1'
    <2>1. SUFFICES ASSUME NEW o \in Ops', o.type = "commit"
                   PROVE  \E b \in Ops' : b.type = "begin" /\ b.txnId = o.txnId /\ b.time < o.time
      BY DEF InvH1
    <2>2. o \in Ops BY <2>1, <1>5, <1>8
    \* Re-bind `o` as a member of the OLD op set before appealing to the unprimed InvH1;
    \* instantiating it directly at an `o \in Ops'` leaves the hypothesis unusable.
    <2>3. PICK oo \in Ops : oo = o BY <2>2
    <2>4. oo.type = "commit" BY <2>3, <2>1
    <2>5. \E b \in Ops : b.type = "begin" /\ b.txnId = oo.txnId /\ b.time < oo.time
      BY <2>3, <2>4 DEF Inv, InvH1
    <2>6. QED BY <2>5, <2>3, <1>5
  \* H2.  Old transactions are untouched (all new ops carry `tid`); the new one is `BodyOps`.
  <1>16. InvH2'
    <2>1. SUFFICES ASSUME NEW t,
                          SI!WritesByTxn(txnHistory', t) # {},
                          NEW rd \in SI!ReadsByTxn(txnHistory', t)
                   PROVE  rd.key \in WKeys(t)'
      BY DEF InvH2
    <2>2. CASE t # tid
      <3>1. /\ SI!WritesByTxn(txnHistory', t) = SI!WritesByTxn(txnHistory, t)
            /\ SI!ReadsByTxn(txnHistory', t)  = SI!ReadsByTxn(txnHistory, t)
        <4>1. {x \in Ops' : x.txnId = t /\ x.type = "write"}
            = {x \in Ops  : x.txnId = t /\ x.type = "write"}
          BY <1>5, <1>6, <2>2
        <4>2. {x \in Ops' : x.txnId = t /\ x.type = "read"}
            = {x \in Ops  : x.txnId = t /\ x.type = "read"}
          BY <1>5, <1>6, <2>2
        <4>3. QED BY <4>1, <4>2 DEF SI!WritesByTxn, SI!ReadsByTxn, Ops
      <3>2. WKeys(t)' = WKeys(t) BY <2>2, <1>12
      <3>3. QED BY <3>1, <3>2, <2>1 DEF Inv, InvH2
    \* The new transaction's reads and writes are exactly the body block's, since `tid` was
    \* fresh; so `BodyOps` is precisely H2 for it.
    <2>3. CASE t = tid
      <3>1. SI!WritesByTxn(txnHistory', tid) = {o \in SI!Range(events) : o.type = "write"}
        <4>1. {x \in Ops' : x.txnId = tid /\ x.type = "write"}
            = {x \in SI!Range(events) : x.type = "write"}
          BY <1>5b, <1>5a, <1>7, <1>2
        <4>2. QED BY <4>1 DEF SI!WritesByTxn, Ops
      <3>2. SI!ReadsByTxn(txnHistory', tid) = {o \in SI!Range(events) : o.type = "read"}
        <4>1. {x \in Ops' : x.txnId = tid /\ x.type = "read"}
            = {x \in SI!Range(events) : x.type = "read"}
          BY <1>5b, <1>5a, <1>7, <1>2
        <4>2. QED BY <4>1 DEF SI!ReadsByTxn, Ops
      <3>3. WKeys(tid)' = {w.key : w \in {o \in SI!Range(events) : o.type = "write"}}
        BY <3>1 DEF WKeys
      <3>4. QED BY <2>1, <2>3, <3>1, <3>2, <3>3, <1>2
    <2>4. QED BY <2>2, <2>3
  \* No new commit op, and no old write set changed, so H3 is inherited verbatim.
  <1>17. InvH3'
    <2>1. SUFFICES ASSUME NEW o1 \in Ops', NEW o2 \in Ops',
                          o1.type = "commit", o2.type = "commit",
                          o1.txnId # o2.txnId,
                          WKeys(o1.txnId)' \cap WKeys(o2.txnId)' # {}
                   PROVE  \/ \E b2 \in Ops' : b2.type = "begin" /\ b2.txnId = o2.txnId
                                              /\ o1.time =< b2.time
                          \/ \E b1 \in Ops' : b1.type = "begin" /\ b1.txnId = o1.txnId
                                              /\ o2.time =< b1.time
      BY DEF InvH3
    <2>2. o1 \in Ops /\ o2 \in Ops BY <2>1, <1>5, <1>8
    <2>3. o1.txnId # tid /\ o2.txnId # tid BY <2>2, <1>7
    <2>4. WKeys(o1.txnId)' = WKeys(o1.txnId) /\ WKeys(o2.txnId)' = WKeys(o2.txnId)
      BY <2>3, <1>12
    <2>5. \/ \E b2 \in Ops : b2.type = "begin" /\ b2.txnId = o2.txnId /\ o1.time =< b2.time
          \/ \E b1 \in Ops : b1.type = "begin" /\ b1.txnId = o1.txnId /\ o2.time =< b1.time
      BY <2>1, <2>2, <2>4 DEF Inv, InvH3
    <2>6. QED BY <2>5, <1>5
  <1>18. QED
    BY <1>9, <1>10, <1>11, <1>13, <1>14, <1>15, <1>16, <1>17 DEF Inv

----------------------------------------------------------------------------------------------------
(**************************************************************************************************)
(*                                                                                                *)
(* Part 13.  The commit step -- where First-Committer-Wins is cashed in.                          *)
(*                                                                                                *)
(* `CommitTxn(tid)` appends one commit op carrying `updatedKeys = WKeys(tid)`.  Reads and writes   *)
(* are untouched, so H2 is inherited.  The two clauses with real content are:                     *)
(*                                                                                                *)
(*   H1 for the new op.  `tid` is running, so `InvRunning` hands us its begin op, stamped at       *)
(*      `r.startTime =< clock < clock + 1`, which is the new commit time.                          *)
(*                                                                                                *)
(*   H3 for the pairs involving the new op.  This is the First-Committer-Wins guard, read          *)
(*      contrapositively.  `TxnCanCommit(tid)` says: there is NO committed op `x` with             *)
(*      `x.time > r.startTime` whose `updatedKeys` meet `WKeys(tid)`.  So any already-committed    *)
(*      `x` sharing a written key has `x.time =< r.startTime = beginOp(tid).time`, which is        *)
(*      exactly H3's "the other one committed no later than I began" disjunct.  `InvCommitKeys`    *)
(*      is what lets `x.updatedKeys` be identified with `WKeys(x.txnId)`, i.e. what connects the   *)
(*      guard's key test to the write ops H3 is stated over.                                       *)
(*                                                                                                *)
(**************************************************************************************************)

THEOREM StepCommit ==
  ASSUME Inv, NEW tid \in TxnIds, CommitTxn(tid)
  PROVE  Inv'
PROOF
  <1> DEFINE o == [type        |-> "commit",
                   txnId       |-> tid,
                   time        |-> clock + 1,
                   updatedKeys |-> SI!KeysWrittenByTxn(txnHistory, tid)]
  <1>1. /\ tid \in SI!RunningTxnIds
        /\ SI!TxnCanCommit(tid)
        /\ txnHistory' = Append(txnHistory, o)
        /\ clock' = clock + 1
        /\ runningTxns' = {r \in runningTxns : r.id # tid}
    BY DEF CommitTxn, SI!CommitTxn
  <1>1a. /\ o.type = "commit"
         /\ o.txnId = tid
         /\ o.time = clock + 1
         /\ o.updatedKeys = SI!KeysWrittenByTxn(txnHistory, tid)
    OBVIOUS
  \* `SI!KeysWrittenByTxn` is `WKeys` -- both are the key set of the transaction's write ops.
  <1>1b. o.updatedKeys = WKeys(tid)
    BY <1>1a DEF SI!KeysWrittenByTxn, WKeys, SI!WritesByTxn
  <1>2. IsSeq(txnHistory') /\ Ops' = Ops \cup {o}
    BY <1>1, OpsAppend DEF Inv, InvSeq
  \* A commit op is neither a read nor a write, so all read/write data is unchanged.
  <1>3. /\ \A t : SI!WritesByTxn(txnHistory', t) = SI!WritesByTxn(txnHistory, t)
        /\ \A t : SI!ReadsByTxn(txnHistory', t)  = SI!ReadsByTxn(txnHistory, t)
        /\ \A t : WKeys(t)' = WKeys(t)
    BY <1>2, <1>1a, RWUnchangedAppend
  \* The committing transaction's running record, and the begin op it points at.
  <1>4. PICK r \in runningTxns : r.id = tid
    BY <1>1 DEF SI!RunningTxnIds
  <1>5. /\ r.startTime \in Nat
        /\ r.startTime =< clock
        /\ \E b \in Ops : b.type = "begin" /\ b.txnId = tid /\ b.time = r.startTime
    BY <1>4 DEF Inv, InvRunning
  <1>6. PICK b \in Ops : b.type = "begin" /\ b.txnId = tid /\ b.time = r.startTime
    BY <1>5
  \* The First-Committer-Wins guard, with its own existential witness discharged.  The witness
  \* `txn` and our `r` are both running records with id `tid`; `InvRunning` pins both of their
  \* start times to the time of `tid`'s unique begin op, so they agree where it matters.
  <1>4a. \A x \in SI!Range(txnHistory) :
           ~(x.type = "commit" /\ x.time > r.startTime /\
             SI!KeysWrittenByTxn(txnHistory, tid) \cap x.updatedKeys # {})
    <2>1. PICK txn \in runningTxns :
            /\ txn.id = tid
            /\ ~\E x \in SI!Range(txnHistory) :
                  /\ x.type = "commit"
                  /\ txn.id = tid /\ x.time > txn.startTime
                  /\ SI!KeysWrittenByTxn(txnHistory, tid) \cap x.updatedKeys # {}
      BY <1>1 DEF SI!TxnCanCommit
    \* Both `txn` and `r` have a begin op for `tid` at their own start time, and begin ops are
    \* unique, so those two begin ops coincide and the start times are equal.
    <2>2. \E bt \in Ops : bt.type = "begin" /\ bt.txnId = tid /\ bt.time = txn.startTime
      BY <2>1 DEF Inv, InvRunning
    <2>3. PICK bt \in Ops : bt.type = "begin" /\ bt.txnId = tid /\ bt.time = txn.startTime
      BY <2>2
    <2>4. bt = b BY <2>3, <1>6 DEF Inv, InvUnique
    <2>5. txn.startTime = r.startTime BY <2>3, <2>4, <1>6
    <2>6. QED BY <2>1, <2>5
  <1>7. clock \in Nat BY DEF Inv, InvClock
  \* `tid` has not committed before: every old commit op names a different transaction.
  \* (InvH1 + InvRunning would also give this, but it follows more directly from the fact that
  \*  a committed transaction is no longer running, which is how CommitTxn removes it.)
  \* `tid` has not committed before: it is still running, and `InvRunning` says a running
  \* transaction has no commit op.  (This is what makes the commit op genuinely new.)
  <1>8. \A x \in Ops : x.type = "commit" => x.txnId # tid
    BY <1>4 DEF Inv, InvRunning
  <1>9. InvSeq' BY <1>2 DEF InvSeq
  <1>10. InvClock'
    <2>1. clock' \in Nat BY <1>1, <1>7
    <2>2. \A x \in Ops : Stamped(x) => (x.time \in Nat /\ x.time =< clock')
      BY <1>1, <1>7 DEF Inv, InvClock
    <2>3. o.time \in Nat /\ o.time =< clock' BY <1>1a, <1>1, <1>7
    <2>4. QED BY <1>2, <2>1, <2>2, <2>3 DEF InvClock
  \* The new op is the only commit op for `tid`, by <1>8; begin ops are untouched.
  <1>11. InvUnique'
    <2>1. SUFFICES ASSUME NEW o1 \in Ops', NEW o2 \in Ops'
                   PROVE  /\ (o1.type = "begin" /\ o2.type = "begin" /\ o1.txnId = o2.txnId)
                             => o1 = o2
                          /\ (o1.type = "commit" /\ o2.type = "commit" /\ o1.txnId = o2.txnId)
                             => o1 = o2
      BY DEF InvUnique
    <2>2. \A x \in Ops' : x.type = "begin" => x \in Ops BY <1>2, <1>1a
    <2>3. QED BY <2>1, <2>2, <1>2, <1>1a, <1>8 DEF Inv, InvUnique
  <1>12. InvCommitKeys'
    <2>1. SUFFICES ASSUME NEW x \in Ops', x.type = "commit"
                   PROVE  x.updatedKeys = WKeys(x.txnId)'
      BY DEF InvCommitKeys
    <2>2. CASE x = o BY <2>2, <1>1b, <1>1a, <1>3
    <2>3. CASE x \in Ops
      <3>1. x.updatedKeys = WKeys(x.txnId) BY <2>3, <2>1 DEF Inv, InvCommitKeys
      <3>2. QED BY <3>1, <1>3
    <2>4. QED BY <2>1, <2>2, <2>3, <1>2
  \* The committing transaction leaves the running set; the rest keep their begin ops.
  <1>13. InvRunning'
    <2>1. SUFFICES ASSUME NEW rr \in runningTxns'
                   PROVE  /\ rr.startTime \in Nat
                          /\ rr.startTime =< clock'
                          /\ \E bb \in Ops' : bb.type = "begin" /\ bb.txnId = rr.id
                                              /\ bb.time = rr.startTime
                          /\ \A x \in Ops' : x.type = "commit" => x.txnId # rr.id
      BY DEF InvRunning
    <2>2. rr \in runningTxns /\ rr.id # tid BY <1>1
    <2>3. /\ rr.startTime \in Nat
          /\ rr.startTime =< clock
          /\ \E bb \in Ops : bb.type = "begin" /\ bb.txnId = rr.id /\ bb.time = rr.startTime
          /\ \A x \in Ops : x.type = "commit" => x.txnId # rr.id
      BY <2>2 DEF Inv, InvRunning
    \* The one new commit op names `tid`, and `rr` is some other still-running transaction.
    <2>4. \A x \in Ops' : x.type = "commit" => x.txnId # rr.id
      BY <2>3, <2>2, <1>2, <1>1a
    <2>5. QED BY <2>3, <2>4, <1>7, <1>1, <1>2
  \* H1 for the new op: `b` is its begin op, at r.startTime =< clock < clock + 1 = o.time.
  <1>14. InvH1'
    <2>1. SUFFICES ASSUME NEW x \in Ops', x.type = "commit"
                   PROVE  \E bb \in Ops' : bb.type = "begin" /\ bb.txnId = x.txnId
                                           /\ bb.time < x.time
      BY DEF InvH1
    <2>2. CASE x = o
      <3>1. b.time < o.time BY <1>6, <1>5, <1>7, <1>1a
      <3>2. b \in Ops' BY <1>6, <1>2
      <3>3. QED BY <2>2, <3>1, <3>2, <1>6, <1>1a
    <2>3. CASE x \in Ops
      <3>1. PICK xx \in Ops : xx = x BY <2>3
      <3>2. xx.type = "commit" BY <3>1, <2>1
      <3>3. \E bb \in Ops : bb.type = "begin" /\ bb.txnId = xx.txnId /\ bb.time < xx.time
        BY <3>1, <3>2 DEF Inv, InvH1
      <3>4. QED BY <3>3, <3>1, <1>2
    <2>4. QED BY <2>1, <2>2, <2>3, <1>2
  <1>15. InvH2' BY <1>3 DEF Inv, InvH2
  (*--------------------------------------------------------------------------------------*)
  (* H3.  Pairs of old commit ops are inherited.  A pair involving the new op is where      *)
  (* First-Committer-Wins is used, in the contrapositive form described in the header.      *)
  (*--------------------------------------------------------------------------------------*)
  <1>16. InvH3'
    <2>1. SUFFICES ASSUME NEW o1 \in Ops', NEW o2 \in Ops',
                          o1.type = "commit", o2.type = "commit",
                          o1.txnId # o2.txnId,
                          WKeys(o1.txnId)' \cap WKeys(o2.txnId)' # {}
                   PROVE  \/ \E b2 \in Ops' : b2.type = "begin" /\ b2.txnId = o2.txnId
                                              /\ o1.time =< b2.time
                          \/ \E b1 \in Ops' : b1.type = "begin" /\ b1.txnId = o1.txnId
                                              /\ o2.time =< b1.time
      BY DEF InvH3
    <2>2. WKeys(o1.txnId) \cap WKeys(o2.txnId) # {} BY <2>1, <1>3
    \* The key sub-argument, stated once and used for whichever side is the new op: if `x` is
    \* an OLD commit op sharing a written key with `tid`, then x.time =< r.startTime = b.time.
    <2>3. ASSUME NEW x \in Ops, x.type = "commit",
                 WKeys(x.txnId) \cap WKeys(tid) # {}
          PROVE  x.time =< b.time
      <3>1. x.updatedKeys = WKeys(x.txnId) BY <2>3 DEF Inv, InvCommitKeys
      <3>2. SI!KeysWrittenByTxn(txnHistory, tid) = WKeys(tid)
        BY DEF SI!KeysWrittenByTxn, WKeys, SI!WritesByTxn
      \* The guard: no committed op later than my start conflicts with my write set.
      \* `SI!TxnCanCommit` picks its own witness out of `runningTxns`; `<1>4a` below identifies
      \* it with `r` (a transaction appears in the running set under one id only).
      <3>3. ~(x.time > r.startTime /\
              SI!KeysWrittenByTxn(txnHistory, tid) \cap x.updatedKeys # {})
        BY <1>4a, <2>3 DEF Ops
      <3>4. SI!KeysWrittenByTxn(txnHistory, tid) \cap x.updatedKeys # {}
        BY <3>1, <3>2, <2>3
      <3>5. ~(x.time > r.startTime) BY <3>3, <3>4
      <3>6. x.time \in Nat BY <2>3 DEF Inv, InvClock, Stamped
      <3>7. QED BY <3>5, <3>6, <1>5, <1>6
    \* Case A: the new op is o1, so the other side is an old commit op sharing a key.
    <2>4. CASE o1 = o /\ o2 \in Ops
      \* Re-bind as a member of the old op set so that <2>3 instantiates.
      <3>0. PICK y \in Ops : y = o2 BY <2>4
      <3>1. y.type = "commit" /\ WKeys(y.txnId) \cap WKeys(tid) # {}
        BY <3>0, <2>1, <2>2, <2>4, <1>1a
      <3>2. o2.time =< b.time BY <3>0, <3>1, <2>3
      <3>3. b \in Ops' /\ b.type = "begin" /\ b.txnId = tid BY <1>6, <1>2
      <3>4. QED BY <3>2, <3>3, <2>4, <1>1a
    \* Case B: symmetric, the new op is o2.
    <2>5. CASE o2 = o /\ o1 \in Ops
      \* Re-bind as a member of the old op set so that <2>3 instantiates.
      <3>0. PICK y \in Ops : y = o1 BY <2>5
      <3>1. y.type = "commit" /\ WKeys(y.txnId) \cap WKeys(tid) # {}
        BY <3>0, <2>1, <2>2, <2>5, <1>1a
      <3>2. o1.time =< b.time BY <3>0, <3>1, <2>3
      <3>3. b \in Ops' /\ b.type = "begin" /\ b.txnId = tid BY <1>6, <1>2
      <3>4. QED BY <3>2, <3>3, <2>5, <1>1a
    \* Case C: both old -- inherited from InvH3.
    <2>6. CASE o1 \in Ops /\ o2 \in Ops
      <3>1. PICK x1 \in Ops : x1 = o1 BY <2>6
      <3>2. PICK x2 \in Ops : x2 = o2 BY <2>6
      <3>3. /\ x1.type = "commit" /\ x2.type = "commit"
            /\ x1.txnId # x2.txnId
            /\ WKeys(x1.txnId) \cap WKeys(x2.txnId) # {}
        BY <3>1, <3>2, <2>1, <2>2
      <3>4. \/ \E b2 \in Ops : b2.type = "begin" /\ b2.txnId = x2.txnId /\ x1.time =< b2.time
            \/ \E b1 \in Ops : b1.type = "begin" /\ b1.txnId = x1.txnId /\ x2.time =< b1.time
        BY <3>1, <3>2, <3>3 DEF Inv, InvH3
      <3>5. QED BY <3>4, <3>1, <3>2, <1>2
    \* `o1 = o2 = o` is impossible: they have different txnIds.
    <2>7. QED BY <2>1, <2>4, <2>5, <2>6, <1>2

  <1>17. QED
    BY <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16 DEF Inv

----------------------------------------------------------------------------------------------------
(**************************************************************************************************)
(*                                                                                                *)
(* Part 14.  Assembly.                                                                            *)
(*                                                                                                *)
(**************************************************************************************************)

\* A stuttering step changes nothing the invariant mentions.
THEOREM StepStutter ==
  ASSUME Inv, UNCHANGED vars
  PROVE  Inv'
PROOF
  <1>1. /\ txnHistory' = txnHistory
        /\ clock'      = clock
        /\ runningTxns' = runningTxns
    BY DEF vars
  <1>2. Ops' = Ops BY <1>1 DEF Ops
  <1>3. QED BY <1>1, <1>2
        DEF Inv, InvSeq, InvClock, InvUnique, InvCommitKeys, InvRunning,
            InvH1, InvH2, InvH3, Ops, WKeys, SI!WritesByTxn, SI!ReadsByTxn

\* The inductive step: a case split over `Next`.
THEOREM Inductive == Inv /\ [Next]_vars => Inv'
PROOF
  <1>1. SUFFICES ASSUME Inv, [Next]_vars PROVE Inv' OBVIOUS
  <1>2. CASE Next
    <2>1. CASE \E tid \in TxnIds, req \in Requests : StartAndRun(tid, req)
      BY <1>1, <2>1, StepStart
    <2>2. CASE \E tid \in TxnIds : CommitTxn(tid)
      BY <1>1, <2>2, StepCommit
    <2>3. CASE \E tid \in TxnIds : AbortTxn(tid)
      BY <1>1, <2>3, StepAbort
    <2>4. CASE AllTxnsDone /\ UNCHANGED vars
      BY <1>1, <2>4, StepStutter
    <2>5. QED BY <1>2, <2>1, <2>2, <2>3, <2>4 DEF Next
  <1>3. CASE UNCHANGED vars
    BY <1>1, <1>3, StepStutter
  <1>4. QED BY <1>1, <1>2, <1>3

(**************************************************************************************************)
(*                                                                                                *)
(* THE RESULT.  Under the robust mix, every reachable history of the auction application running  *)
(* on snapshot isolation is conflict serializable.                                                *)
(*                                                                                                *)
(**************************************************************************************************)
THEOREM Safety == Spec => []SerializableViaPath
PROOF
  <1>1. Init => Inv BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv' BY Inductive
  <1>3. Inv => SerializableViaPath BY InvImpliesSerializable
  <1>4. QED BY <1>1, <1>2, <1>3, PTL DEF Spec

====
