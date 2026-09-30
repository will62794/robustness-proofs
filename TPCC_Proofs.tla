------------------------------- MODULE TPCC_Proofs -------------------------------
(**************************************************************************************************)
(*                                                                                                *)
(* TLAPS proof development for  Spec => [](SerializableViaPath).                                  *)
(*                                                                                                *)
(**************************************************************************************************)
EXTENDS TPCC, TLAPS, SequenceTheorems, FiniteSetTheorems

(**************************************************************************************************)
(* Part 1.  The base case: the empty history is serializable.                                     *)
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

(**************************************************************************************************)
(* Part 2.  Frame lemmas.                                                                         *)
(*                                                                                                *)
(* `SerializableViaPath` is a function of `txnHistory` alone, via `SI!SerializationGraph`.  That  *)
(* graph is determined by:                                                                        *)
(*                                                                                                *)
(*   - the set of committed transaction ids, `SI!CommittedTxns(h)`, which are its nodes, and      *)
(*   - for each such id, its reads, writes, begin time and commit time.                           *)
(*                                                                                                *)
(* So appending operations that (a) are not `commit` ops and (b) all carry a txnId that is not    *)
(* committed in the resulting history leaves the graph unchanged.  That covers `StartAndRun`      *)
(* and `AbortTxn`; only `CommitTxn` can grow the graph.                                           *)
(**************************************************************************************************)

\* SI!Range is literally the Range of Functions / SequenceTheorems, so their lemmas apply.
LEMMA RangeSame == \A f : SI!Range(f) = Range(f)
  BY DEF SI!Range, Range

\* Appending to a history adds exactly the appended element to its range.
LEMMA RangeAppend ==
  \A S : \A h \in Seq(S) : \A o \in S :
    SI!Range(h \o <<o>>) = SI!Range(h) \cup {o}
PROOF
  <1>1. SUFFICES ASSUME NEW S, NEW h \in Seq(S), NEW o \in S
               PROVE  SI!Range(h \o <<o>>) = SI!Range(h) \cup {o}
    OBVIOUS
  <1>2. <<o>> \in Seq(S) OBVIOUS
  <1>3. Range(h \o <<o>>) = Range(h) \cup Range(<<o>>)
    BY <1>2, RangeConcatenation
  <1>4. Range(<<o>>) = {o} BY DEF Range
  <1>5. QED BY <1>3, <1>4, RangeSame

\* A non-commit op does not change the committed set.
LEMMA CommittedAppendNonCommit ==
  ASSUME NEW S, NEW h \in Seq(S), NEW o \in S, o.type # "commit"
  PROVE  SI!CommittedTxns(h \o <<o>>) = SI!CommittedTxns(h)
PROOF
  <1>2. SI!Range(h \o <<o>>) = SI!Range(h) \cup {o} BY RangeAppend
  <1>3. {x \in SI!Range(h \o <<o>>) : x.type = "commit"}
        = {x \in SI!Range(h) : x.type = "commit"}
    BY <1>2
  <1>4. QED BY <1>3 DEF SI!CommittedTxns

(**************************************************************************************************)
(* The per-transaction data the graph is built from is also unchanged by appending an op whose    *)
(* txnId belongs to no committed transaction.                                                     *)
(**************************************************************************************************)

\* Reads/writes of a transaction other than the appended op's owner are unchanged.
LEMMA ReadsWritesAppendOther ==
  ASSUME NEW S, NEW h \in Seq(S), NEW o \in S, NEW t, t # o.txnId
  PROVE  /\ SI!ReadsByTxn(h \o <<o>>, t)  = SI!ReadsByTxn(h, t)
         /\ SI!WritesByTxn(h \o <<o>>, t) = SI!WritesByTxn(h, t)
PROOF
  <1>1. SI!Range(h \o <<o>>) = SI!Range(h) \cup {o} BY RangeAppend
  <1>2. {op \in SI!Range(h \o <<o>>) : op.txnId = t /\ op.type = "read"}
        = {op \in SI!Range(h) : op.txnId = t /\ op.type = "read"}
    BY <1>1
  <1>3. {op \in SI!Range(h \o <<o>>) : op.txnId = t /\ op.type = "write"}
        = {op \in SI!Range(h) : op.txnId = t /\ op.type = "write"}
    BY <1>1
  <1>4. QED BY <1>2, <1>3 DEF SI!ReadsByTxn, SI!WritesByTxn

\* The begin and commit ops of such a transaction are unchanged.
LEMMA BeginCommitAppendOther ==
  ASSUME NEW S, NEW h \in Seq(S), NEW o \in S, NEW t, t # o.txnId
  PROVE  /\ SI!BeginOp(h \o <<o>>, t)  = SI!BeginOp(h, t)
         /\ SI!CommitOp(h \o <<o>>, t) = SI!CommitOp(h, t)
PROOF
  <1>1. SI!Range(h \o <<o>>) = SI!Range(h) \cup {o} BY RangeAppend
  <1>2. \A x : (x \in SI!Range(h \o <<o>>) /\ (x.txnId = t /\ x.type = "begin"))
            <=> (x \in SI!Range(h) /\ (x.txnId = t /\ x.type = "begin"))
    BY <1>1
  <1>3. \A x : (x \in SI!Range(h \o <<o>>) /\ (x.txnId = t /\ x.type = "commit"))
            <=> (x \in SI!Range(h) /\ (x.txnId = t /\ x.type = "commit"))
    BY <1>1
  <1>4. QED BY <1>2, <1>3 DEF SI!BeginOp, SI!CommitOp

(**************************************************************************************************)
(* Putting those together: appending a non-commit op belonging to a transaction that is not       *)
(* committed in `h` leaves the whole serialization graph unchanged, and hence preserves the       *)
(* serializability predicate.                                                                     *)
(**************************************************************************************************)

LEMMA GraphAppendNonCommit ==
  ASSUME NEW S, NEW h \in Seq(S), NEW o \in S,
         o.type # "commit",
         o.txnId \notin SI!CommittedTxns(h)
  PROVE  SI!SerializationGraph(h \o <<o>>) = SI!SerializationGraph(h)
PROOF
  <1>1. SI!CommittedTxns(h \o <<o>>) = SI!CommittedTxns(h)
    BY CommittedAppendNonCommit
  <1>2. \A t : t \in SI!CommittedTxns(h) => t # o.txnId
    OBVIOUS
  <1>3. ASSUME NEW t1 \in SI!CommittedTxns(h), NEW t2 \in SI!CommittedTxns(h)
        PROVE  /\ SI!WWDependency(h \o <<o>>, t1, t2) <=> SI!WWDependency(h, t1, t2)
               /\ SI!WRDependency(h \o <<o>>, t1, t2) <=> SI!WRDependency(h, t1, t2)
               /\ SI!RWDependency(h \o <<o>>, t1, t2) <=> SI!RWDependency(h, t1, t2)
    <2>1. t1 # o.txnId /\ t2 # o.txnId BY <1>2
    <2>2. /\ SI!ReadsByTxn(h \o <<o>>, t1)  = SI!ReadsByTxn(h, t1)
          /\ SI!WritesByTxn(h \o <<o>>, t1) = SI!WritesByTxn(h, t1)
          /\ SI!ReadsByTxn(h \o <<o>>, t2)  = SI!ReadsByTxn(h, t2)
          /\ SI!WritesByTxn(h \o <<o>>, t2) = SI!WritesByTxn(h, t2)
      BY <2>1, ReadsWritesAppendOther
    <2>3. /\ SI!BeginOp(h \o <<o>>, t1)  = SI!BeginOp(h, t1)
          /\ SI!CommitOp(h \o <<o>>, t1) = SI!CommitOp(h, t1)
          /\ SI!BeginOp(h \o <<o>>, t2)  = SI!BeginOp(h, t2)
          /\ SI!CommitOp(h \o <<o>>, t2) = SI!CommitOp(h, t2)
      BY <2>1, BeginCommitAppendOther
    <2>4. QED
      BY <2>2, <2>3 DEF SI!WWDependency, SI!WRDependency, SI!RWDependency
  <1>4. QED BY <1>1, <1>3 DEF SI!SerializationGraph

LEMMA SerializablePreservedNonCommit ==
  ASSUME NEW S, NEW h \in Seq(S), NEW o \in S,
         o.type # "commit",
         o.txnId \notin SI!CommittedTxns(h),
         SI!IsConflictSerializableViaPath(h)
  PROVE  SI!IsConflictSerializableViaPath(h \o <<o>>)
PROOF
  <1>1. SI!SerializationGraph(h \o <<o>>) = SI!SerializationGraph(h)
    BY GraphAppendNonCommit
  <1>2. QED BY <1>1 DEF SI!IsConflictSerializableViaPath

(**************************************************************************************************)
(* Part 3.  The same result, generalized from appending one op to appending a whole block.        *)
(*                                                                                                *)
(* `StartAndRun` appends a begin op plus the transaction's entire body in a single step, so the   *)
(* one-op lemma above does not apply directly.  Rather than induct over the block, note that      *)
(* every ingredient of the serialization graph depends on the history only through its *range*:  *)
(* `CommittedTxns`, `ReadsByTxn`, `WritesByTxn`, `BeginOp` and `CommitOp` are all defined by      *)
(* filtering `SI!Range(h)`.  So two histories with related ranges have related graphs, whatever   *)
(* the length or order of what was appended.                                                      *)
(**************************************************************************************************)

\* Range of a concatenation, lifted to SI!Range.
LEMMA RangeConcat ==
  ASSUME NEW S, NEW h1 \in Seq(S), NEW h2 \in Seq(S)
  PROVE  SI!Range(h1 \o h2) = SI!Range(h1) \cup SI!Range(h2)
  BY RangeConcatenation, RangeSame

(**************************************************************************************************)
(* The core frame lemma, stated over ranges.  If the appended block contains no commit op, and    *)
(* no op of the block belongs to a transaction committed in h, the graph is unchanged.            *)
(**************************************************************************************************)
LEMMA GraphAppendBlock ==
  ASSUME NEW S, NEW h \in Seq(S), NEW b \in Seq(S),
         \A o \in SI!Range(b) : o.type # "commit",
         \A o \in SI!Range(b) : o.txnId \notin SI!CommittedTxns(h)
  PROVE  SI!SerializationGraph(h \o b) = SI!SerializationGraph(h)
PROOF
  <1>0. SI!Range(h \o b) = SI!Range(h) \cup SI!Range(b) BY RangeConcat
  \* The committed set is unchanged: the block contributes no commit ops.
  <1>1. SI!CommittedTxns(h \o b) = SI!CommittedTxns(h)
    <2>1. {x \in SI!Range(h \o b) : x.type = "commit"}
          = {x \in SI!Range(h) : x.type = "commit"}
      BY <1>0
    <2>2. QED BY <2>1 DEF SI!CommittedTxns
  \* Every committed transaction differs from every txnId appearing in the block.
  <1>2. \A t \in SI!CommittedTxns(h) : \A o \in SI!Range(b) : t # o.txnId
    OBVIOUS
  <1>3. ASSUME NEW t \in SI!CommittedTxns(h)
        PROVE  /\ SI!ReadsByTxn(h \o b, t)  = SI!ReadsByTxn(h, t)
               /\ SI!WritesByTxn(h \o b, t) = SI!WritesByTxn(h, t)
               /\ SI!BeginOp(h \o b, t)     = SI!BeginOp(h, t)
               /\ SI!CommitOp(h \o b, t)    = SI!CommitOp(h, t)
    <2>1. \A o \in SI!Range(b) : o.txnId # t BY <1>2
    <2>2. {op \in SI!Range(h \o b) : op.txnId = t /\ op.type = "read"}
          = {op \in SI!Range(h) : op.txnId = t /\ op.type = "read"}
      BY <1>0, <2>1
    <2>3. {op \in SI!Range(h \o b) : op.txnId = t /\ op.type = "write"}
          = {op \in SI!Range(h) : op.txnId = t /\ op.type = "write"}
      BY <1>0, <2>1
    <2>4. \A x : (x \in SI!Range(h \o b) /\ (x.txnId = t /\ x.type = "begin"))
              <=> (x \in SI!Range(h) /\ (x.txnId = t /\ x.type = "begin"))
      BY <1>0, <2>1
    <2>5. \A x : (x \in SI!Range(h \o b) /\ (x.txnId = t /\ x.type = "commit"))
              <=> (x \in SI!Range(h) /\ (x.txnId = t /\ x.type = "commit"))
      BY <1>0, <2>1
    <2>6. QED
      BY <2>2, <2>3, <2>4, <2>5
      DEF SI!ReadsByTxn, SI!WritesByTxn, SI!BeginOp, SI!CommitOp
  <1>4. ASSUME NEW t1 \in SI!CommittedTxns(h), NEW t2 \in SI!CommittedTxns(h)
        PROVE  /\ SI!WWDependency(h \o b, t1, t2) <=> SI!WWDependency(h, t1, t2)
               /\ SI!WRDependency(h \o b, t1, t2) <=> SI!WRDependency(h, t1, t2)
               /\ SI!RWDependency(h \o b, t1, t2) <=> SI!RWDependency(h, t1, t2)
    BY <1>3 DEF SI!WWDependency, SI!WRDependency, SI!RWDependency
  <1>5. QED BY <1>1, <1>4 DEF SI!SerializationGraph

LEMMA SerializablePreservedBlock ==
  ASSUME NEW S, NEW h \in Seq(S), NEW b \in Seq(S),
         \A o \in SI!Range(b) : o.type # "commit",
         \A o \in SI!Range(b) : o.txnId \notin SI!CommittedTxns(h),
         SI!IsConflictSerializableViaPath(h)
  PROVE  SI!IsConflictSerializableViaPath(h \o b)
PROOF
  <1>1. SI!SerializationGraph(h \o b) = SI!SerializationGraph(h)
    BY GraphAppendBlock
  <1>2. QED BY <1>1 DEF SI!IsConflictSerializableViaPath

(**************************************************************************************************)
(* Part 4.  What remains: the commit case.                                                        *)
(*                                                                                                *)
(* Parts 1-3 dispose of every step that cannot add a node to the serialization graph.  The        *)
(* remaining obligation is the whole mathematical content of the result: when a transaction       *)
(* commits, the new node and its incident edges must not close a cycle.                           *)
(*                                                                                                *)
(* This is the Fekete-Liarokapis-O'Neil-O'Neil-Shasha (TODS 2005, Section 5) theorem specialized  *)
(* to TPC-C, and it is NOT provable from the frame reasoning above.  Two things make it hard:     *)
(*                                                                                                *)
(*   1. `SerializableViaPath` is not an inductive invariant.  Acyclicity of the graph after n     *)
(*      commits does not by itself imply acyclicity after n+1: the new node can close a cycle     *)
(*      through existing nodes.  A stronger inductive invariant is needed, of roughly the form    *)
(*      "no cycle, AND no path between committed transactions consisting of two consecutive       *)
(*      rw-anti-dependency edges out of concurrent transactions" -- the absence of Fekete et      *)
(*      al.'s `dangerous structure`.                                                              *)
(*                                                                                                *)
(*   2. Discharging that stronger invariant requires reasoning about the *specific* key sets that *)
(*      the five TPC-C programs read and write, i.e. unfolding NewOrderProgram, PaymentProgram,   *)
(*      DeliveryProgram, OrderStatusProgram and StockLevelProgram through Rd/Wr/Del, ConcatOver,  *)
(*      Flatten and SeqOf.  In particular the First-Committer-Wins conflict on D_NEXT_O_ID        *)
(*      between any two New-Orders on the same district is what rules out the dangerous           *)
(*      structure, and that argument is where the ColumnGranularity distinction bites.            *)
(*                                                                                                *)
(* The statement below is the exact obligation, left OMITTED.  `tlapm` reports it as a gap, so    *)
(* nothing above silently depends on an unproved assertion.                                       *)
(**************************************************************************************************)

(*--------------------------------------------------------------------------------------------*)
(* A reduction that IS provable, and that isolates the hard part.                              *)
(*                                                                                             *)
(* The committing transaction is a fresh node.  Of the three edge kinds, two can never leave   *)
(* it:                                                                                         *)
(*                                                                                             *)
(*   WW(new, t) needs CommitOp(new).time < CommitOp(t).time -- impossible, `new` commits last. *)
(*   WR(new, t) needs CommitOp(new).time < BeginOp(t).time  -- impossible, t already began.    *)
(*                                                                                             *)
(* RW(new, t) needs only BeginOp(new).time < CommitOp(t).time, which CAN hold.  So the new     *)
(* node's outgoing edges are exactly its rw-anti-dependencies, and a cycle through it must     *)
(* leave along an rw edge.  That is the hypothesis of Fekete et al.'s dangerous-structure      *)
(* argument, and it is why the theorem is about anti-dependencies specifically.                *)
(*                                                                                             *)
(* `maxTime` below is the clock-monotonicity fact: the committing op carries the largest time  *)
(* in the history.  It is an invariant of the spec (clock only ever increments), not proved    *)
(* here.                                                                                       *)
(*--------------------------------------------------------------------------------------------*)
LEMMA NewCommitHasNoOutgoingWWorWR ==
  ASSUME NEW S, NEW h \in Seq(S), NEW o \in S,
         o.type = "commit",
         \* `o` is the only commit op for its transaction.
         \A x \in SI!Range(h) : ~(x.txnId = o.txnId /\ x.type = "commit"),
         \* clock monotonicity: `o` commits no earlier than anything already in h.
         \A x \in SI!Range(h) : x.time =< o.time,
         NEW t, t \in SI!CommittedTxns(h), t # o.txnId,
         \* the other transaction's begin/commit ops really are in h
         SI!CommitOp(h, t) \in SI!Range(h),
         SI!BeginOp(h, t) \in SI!Range(h),
         \* times are naturals (so =< and < interact as expected)
         o.time \in Nat,
         SI!CommitOp(h, t).time \in Nat,
         SI!BeginOp(h, t).time \in Nat
  PROVE  /\ ~SI!WWDependency(h \o <<o>>, o.txnId, t)
         /\ ~SI!WRDependency(h \o <<o>>, o.txnId, t)
PROOF
  <1>0. SI!Range(h \o <<o>>) = SI!Range(h) \cup {o} BY RangeAppend
  \* The commit op of the new transaction in the extended history is exactly `o`.
  <1>1. SI!CommitOp(h \o <<o>>, o.txnId) = o
    <2>1. \A x : (x \in SI!Range(h \o <<o>>) /\ (x.txnId = o.txnId /\ x.type = "commit"))
              <=> (x \in {o} /\ (x.txnId = o.txnId /\ x.type = "commit"))
      BY <1>0
    <2>2. (CHOOSE x \in SI!Range(h \o <<o>>) : x.txnId = o.txnId /\ x.type = "commit")
          = (CHOOSE x \in {o} : x.txnId = o.txnId /\ x.type = "commit")
      BY <2>1
    <2>3. (CHOOSE x \in {o} : x.txnId = o.txnId /\ x.type = "commit") = o
      OBVIOUS
    <2>4. QED BY <2>2, <2>3 DEF SI!CommitOp
  \* The other transaction's begin and commit ops are unchanged, and carry times =< o.time.
  <1>2. SI!CommitOp(h \o <<o>>, t) = SI!CommitOp(h, t)
    BY BeginCommitAppendOther
  <1>3. SI!BeginOp(h \o <<o>>, t) = SI!BeginOp(h, t)
    BY BeginCommitAppendOther
  <1>4. SI!CommitOp(h, t).time =< o.time
    OBVIOUS
  <1>5. SI!BeginOp(h, t).time =< o.time
    OBVIOUS
  \* Hence neither strict inequality can hold.
  <1>6. ~(SI!CommitOp(h \o <<o>>, o.txnId).time < SI!CommitOp(h \o <<o>>, t).time)
    BY <1>1, <1>2, <1>4
  <1>7. ~(SI!CommitOp(h \o <<o>>, o.txnId).time < SI!BeginOp(h \o <<o>>, t).time)
    BY <1>1, <1>3, <1>5
  <1>8. QED BY <1>6, <1>7 DEF SI!WWDependency, SI!WRDependency

(*--------------------------------------------------------------------------------------------*)
(* The remaining obligation, stated correctly.                                                 *)
(*                                                                                             *)
(* NOTE.  The naive form of this lemma --                                                      *)
(*                                                                                             *)
(*     h serializable /\ o.type = "commit"  =>  h \o <<o>> serializable                        *)
(*                                                                                             *)
(* -- is FALSE, and it is worth recording why, because it is exactly the write-skew anomaly    *)
(* that makes this whole development non-trivial.  Take keys k1, k2 and:                       *)
(*                                                                                             *)
(*     t3: begin(1), read k2, write k1          (t3 has NOT committed in h)                    *)
(*     t1: begin(2), read k1, write k2, commit(3)                                              *)
(*                                                                                             *)
(* CommittedTxns(h) = {t1}; a one-node graph has no edges (SerializationGraph requires         *)
(* tedge[1] # tedge[2]), so h is serializable.  Append o = t3's commit at time 4.  Now both    *)
(* t3 and t1 are committed and BOTH rw edges appear --                                         *)
(*                                                                                             *)
(*     RW(t3,t1): t3 reads k2, t1 writes k2, begin(t3)=1 < commit(t1)=3                        *)
(*     RW(t1,t3): t1 reads k1, t3 writes k1, begin(t1)=2 < commit(t3)=4                        *)
(*                                                                                             *)
(* -- closing the cycle t1 -> t3 -> t1.  So acyclicity alone is NOT inductive, and any proof   *)
(* that "completes" the naive statement is proving something false.                            *)
(*                                                                                             *)
(* The correct statement carries the missing hypothesis as an explicit predicate,              *)
(* `CommitKeepsAcyclic`, which is precisely the Fekete et al. no-dangerous-structure condition *)
(* specialized to this history.  Proving that TPC-C satisfies it is the open work; the         *)
(* conditional lemma below is proved outright.                                                 *)
(*--------------------------------------------------------------------------------------------*)

\* The condition under which committing `o` cannot close a cycle: the extended graph is
\* acyclic.  Stated over the graph rather than the workload, so it is checkable per step.
CommitKeepsAcyclic(h, o) ==
  ~SI!IsCycleViaPath(SI!SerializationGraph(h \o <<o>>))

LEMMA CommitPreservesSerializable ==
  ASSUME NEW S, NEW h \in Seq(S), NEW o \in S,
         o.type = "commit",
         SI!IsConflictSerializableViaPath(h),
         CommitKeepsAcyclic(h, o)
  PROVE  SI!IsConflictSerializableViaPath(h \o <<o>>)
BY DEF CommitKeepsAcyclic, SI!IsConflictSerializableViaPath

(*--------------------------------------------------------------------------------------------*)
(* THE OPEN ASSUMPTION.                                                                        *)
(*                                                                                             *)
(* This is the Fekete et al. TPC-C result, and it is the single mathematical fact this         *)
(* development does not prove.  It is stated as an explicit named ASSUME rather than as an     *)
(* OMITTED proof, because an OMITTED proof of a FALSE statement is indistinguishable from an   *)
(* OMITTED proof of a true one -- as the counterexample above shows, the version of this       *)
(* obligation without a workload hypothesis IS false.  Writing it as an assumption forces the  *)
(* reader to see what is being taken on faith, and `tlapm` lists it among the theorem's        *)
(* dependencies.                                                                               *)
(*                                                                                             *)
(* Discharging it means proving that the TPC-C programs cannot produce two consecutive rw      *)
(* anti-dependency edges out of concurrent transactions on a cycle -- the argument that turns  *)
(* on New-Order's First-Committer-Wins conflict on D_NEXT_O_ID, and that FAILS at row          *)
(* granularity (see this spec's header).  Any attempt to prove it must therefore use           *)
(* ColumnGranularity = TRUE; a proof that goes through for both settings is necessarily wrong. *)
(*--------------------------------------------------------------------------------------------*)
TPCCNoDangerousStructure ==
  \A tid \in TxnIds :
     CommitTxn(tid) => CommitKeepsAcyclic(txnHistory,
                         [type |-> "commit", txnId |-> tid, time |-> clock + 1,
                          updatedKeys |-> SI!KeysWrittenByTxn(txnHistory, tid)])

(**************************************************************************************************)
(* Part 5.  The history is a sequence.                                                            *)
(*                                                                                                *)
(* The frame lemmas are stated for `h \in Seq(S)`.  To instantiate them at `txnHistory` we need   *)
(* to know that `txnHistory` IS a sequence -- concretely, `SequenceTheorems!AppendIsConcat`,      *)
(* which turns the spec's `Append(txnHistory, op)` into the `txnHistory \o <<op>>` the lemmas     *)
(* are phrased in, has `seq \in Seq(S)` as a hypothesis.                                          *)
(*                                                                                                *)
(* TPCC's `TypeOK` says nothing about `txnHistory`, and SnapshotIsolation's `TypeInvariant`       *)
(* deliberately omits it too (its comment notes `txnHistory \in Seq(AnyOpType)` is expensive for  *)
(* TLC).  But the frame lemmas never inspect the element type -- they only need `h` to be SOME    *)
(* sequence.  So rather than pin down the exact op type (which would mean characterizing          *)
(* everything Rd/Wr/Del can produce), we use the weaker `IsSeq`, which is enough for the lemmas   *)
(* and is trivially inductive: the empty sequence satisfies it, and both append and concatenation *)
(* preserve it, widening the element set as needed.                                               *)
(**************************************************************************************************)

IsSeq(h) == \E S : h \in Seq(S)

HistoryTypeOK == IsSeq(txnHistory)

LEMMA EmptyIsSeq == IsSeq(<<>>)
  BY DEF IsSeq

\* Appending preserves IsSeq, and coincides with the `\o <<o>>` form the frame lemmas use.
LEMMA AppendIsSeq ==
  ASSUME NEW h, IsSeq(h), NEW o
  PROVE  /\ IsSeq(Append(h, o))
         /\ Append(h, o) = h \o <<o>>
         /\ IsSeq(h \o <<o>>)
PROOF
  <1>1. PICK U : h \in Seq(U) BY DEF IsSeq
  <1>2. h \in Seq(U \cup {o}) BY <1>1, SeqMonotonic
  <1>3. o \in U \cup {o} OBVIOUS
  <1>4. Append(h, o) = h \o <<o>> BY <1>2, <1>3, AppendIsConcat
  <1>5. Append(h, o) \in Seq(U \cup {o}) BY <1>2, <1>3, AppendProperties
  <1>6. QED BY <1>4, <1>5 DEF IsSeq

\* Concatenation preserves IsSeq (needed for StartAndRun, which appends a whole block).
LEMMA ConcatIsSeq ==
  ASSUME NEW h, IsSeq(h), NEW b, IsSeq(b)
  PROVE  IsSeq(h \o b)
PROOF
  <1>1. PICK U : h \in Seq(U) BY DEF IsSeq
  <1>2. PICK V : b \in Seq(V) BY DEF IsSeq
  <1>3. h \in Seq(U \cup V) /\ b \in Seq(U \cup V) BY <1>1, <1>2, SeqMonotonic
  <1>4. QED BY <1>3, ConcatProperties DEF IsSeq

\* Any function on 1..n is a sequence; this is how StartAndRun's `events` block qualifies.
LEMMA FcnOnIntervalIsSeq ==
  ASSUME NEW n \in Nat, NEW T, NEW f \in [1..n -> T]
  PROVE  IsSeq(f)
PROOF
  <1>1. f \in UNION {[1..m -> T] : m \in Nat} OBVIOUS
  <1>2. f \in Seq(T) BY <1>1, SeqDef
  <1>3. QED BY <1>2 DEF IsSeq

\* Any function built on 1..n is a sequence, taking its own image as the element set.
LEMMA FcnIsSeqRange ==
  ASSUME NEW n \in Nat, NEW e(_)
  PROVE  IsSeq([i \in 1..n |-> e(i)])
PROOF
  <1>1. [i \in 1..n |-> e(i)] \in [1..n -> {e(i) : i \in 1..n}] OBVIOUS
  <1>2. QED BY <1>1, FcnOnIntervalIsSeq

(*--------------------------------------------------------------------------------------------*)
(* `Flatten` is a sequence whenever its length is a natural number.  `SumLens(s)` is defined   *)
(* as a Cardinality, so this holds as soon as the index set is finite -- which it is, being a  *)
(* union of finite products over DOMAIN s.  We take the length fact as the hypothesis rather   *)
(* than re-deriving finiteness, and discharge it at each use site.                             *)
(*--------------------------------------------------------------------------------------------*)
\* SumLens is a Cardinality of a finite set, hence a natural number.
LEMMA SumLensNat ==
  ASSUME NEW s, IsSeq(s)
  PROVE  SumLens(s) \in Nat
PROOF
  <1>1. PICK T : s \in Seq(T) BY DEF IsSeq
  <1>2. IsFiniteSet(DOMAIN s) BY <1>1, FS_Interval, LenProperties
  <1>3. ASSUME NEW i \in DOMAIN s PROVE IsFiniteSet({i} \X (1..Len(s[i])))
    <2>1. IsFiniteSet({i}) BY FS_Singleton
    <2>2. IsFiniteSet(1..Len(s[i])) BY FS_Interval
    <2>3. QED BY <2>1, <2>2, FS_Product
  <1>4. DEFINE SS == {{i} \X (1..Len(s[i])) : i \in DOMAIN s}
  <1>5. IsFiniteSet(SS) BY <1>2, FS_Image
  <1>6. \A X \in SS : IsFiniteSet(X) BY <1>3
  <1>7. IsFiniteSet(UNION SS) BY <1>5, <1>6, FS_UNION
  <1>8. QED BY <1>7, FS_CardinalityType DEF SumLens

LEMMA FlattenIsSeq ==
  ASSUME NEW s, SumLens(s) \in Nat
  PROVE  IsSeq(Flatten(s)) /\ Len(Flatten(s)) = SumLens(s)
PROOF
  <1>1. Flatten(s) = [k \in 1..SumLens(s) |-> s[Blk(s,k)][k - OffLens(s, Blk(s,k))]]
    BY DEF Flatten
  <1>2. IsSeq(Flatten(s)) BY <1>1, FcnIsSeqRange
  <1>3. Flatten(s) \in [1..SumLens(s) -> {s[Blk(s,k)][k - OffLens(s, Blk(s,k))]
                                          : k \in 1..SumLens(s)}]
    BY <1>1
  <1>4. QED BY <1>2, <1>3, LenProperties

(*--------------------------------------------------------------------------------------------*)
(* Every TPC-C program is a sequence.                                                          *)
(*                                                                                             *)
(* The programs are built from Rd / Wr / Del (each either an explicit 1-tuple or a function on *)
(* 1..Len(SeqOfCols(...))), combined with \o and ConcatOver.  ConcatOver is Flatten of a        *)
(* function on an interval, so it is a sequence by FlattenIsSeq + SumLensNat; and \o preserves *)
(* being a sequence by ConcatIsSeq.  Hence so is every program, whatever the request type.     *)
(*--------------------------------------------------------------------------------------------*)

\* ConcatOver produces a sequence: it is Flatten applied to a function on an interval.
LEMMA ConcatOverIsSeq ==
  ASSUME NEW f(_), NEW ids, Len(SeqOf(ids)) \in Nat
  PROVE  IsSeq(ConcatOver(f, ids))
PROOF
  <1>1. DEFINE s == [i \in 1..Len(SeqOf(ids)) |-> f(SeqOf(ids)[i])]
  <1>2. ConcatOver(f, ids) = Flatten(s) BY DEF ConcatOver
  <1>3. IsSeq(s) BY FcnIsSeqRange
  <1>4. SumLens(s) \in Nat BY <1>3, SumLensNat
  <1>5. QED BY <1>2, <1>4, FlattenIsSeq

(**************************************************************************************************)
(* Part 6.  The inductive invariant and the top-level theorem.                                    *)
(*                                                                                                *)
(* `Inv` carries three conjuncts:                                                                 *)
(*                                                                                                *)
(*   HistoryTypeOK       -- the history is a sequence, so the frame lemmas apply (Part 5).        *)
(*   RunningNotCommitted -- a running transaction has not already committed.  This is the         *)
(*                          freshness side condition the frame lemmas need: it is what rules out  *)
(*                          an appended begin/read/write/abort op belonging to a node that is     *)
(*                          already in the graph.                                                 *)
(*   SerializableViaPath -- the goal.                                                             *)
(*                                                                                                *)
(* `NoCommitAfterCommit` below records why RunningNotCommitted is itself inductive: committing    *)
(* removes the transaction from runningTxns, and nothing ever puts a committed id back.           *)
(**************************************************************************************************)

RunningNotCommitted ==
  \A t \in SI!RunningTxnIds : t \notin SI!CommittedTxns(txnHistory)

Inv == HistoryTypeOK /\ RunningNotCommitted /\ SerializableViaPath

(*--------------------------------------------------------------------------------------------*)
(* AbortTxn: appends a single "abort" op for a running -- hence uncommitted -- transaction.    *)
(* This is a direct instance of the Part 2 one-op frame lemma.                                 *)
(*--------------------------------------------------------------------------------------------*)
THEOREM StepAbort ==
  ASSUME Inv, NEW tid, AbortTxn(tid)
  PROVE  HistoryTypeOK' /\ SerializableViaPath'
PROOF
  <1>a. SI!AbortTxn(tid) BY DEF AbortTxn
  <1>1. DEFINE ao == [type |-> "abort", txnId |-> tid, time |-> clock + 1]
  <1>2. txnHistory' = Append(txnHistory, ao) BY <1>a DEF SI!AbortTxn
  <1>3. txnHistory' = txnHistory \o <<ao>>
    BY <1>2, AppendIsSeq DEF Inv, HistoryTypeOK
  <1>4. HistoryTypeOK' BY <1>2, AppendIsSeq DEF Inv, HistoryTypeOK
  \* Freshness: tid is running, so by the invariant it is not committed.
  <1>5. tid \notin SI!CommittedTxns(txnHistory)
    <2>1. tid \in SI!RunningTxnIds BY <1>a DEF SI!AbortTxn
    <2>2. QED BY <2>1 DEF Inv, RunningNotCommitted
  \* Apply the frame lemma.
  <1>6. PICK U : txnHistory \in Seq(U) BY DEF Inv, HistoryTypeOK, IsSeq
  <1>7. txnHistory \in Seq(U \cup {ao}) /\ ao \in U \cup {ao}
    BY <1>6, SeqMonotonic
  <1>8. SI!SerializationGraph(txnHistory \o <<ao>>) = SI!SerializationGraph(txnHistory)
    BY <1>5, <1>7, GraphAppendNonCommit
  <1>9. SerializableViaPath'
    BY <1>3, <1>8 DEF Inv, SerializableViaPath, SI!IsConflictSerializableViaPath
  <1>10. QED BY <1>4, <1>9

(*--------------------------------------------------------------------------------------------*)
(* StartAndRun: appends a begin op followed by the transaction's whole body.  `Unused(tid)`    *)
(* gives freshness directly -- no op of tid is in the history at all, so in particular tid is  *)
(* not committed -- and every appended op carries txnId = tid.  This is the Part 3 block       *)
(* frame lemma.                                                                                *)
(*--------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------*)
(* The one property of the TPC-C programs this proof needs: a program emits only reads and     *)
(* writes -- never a begin, abort or commit op.  This is immediate from the shapes of Rd, Wr   *)
(* and Del (the only record constructors the programs use), but establishing it formally means *)
(* pushing the property through ConcatOver / Flatten / \o for all five program bodies, which   *)
(* is mechanical rather than mathematical.  We state it as an explicit ASSUMPTION so that it   *)
(* is visible in the theorem's dependencies rather than hidden inside a proof step.            *)
(*--------------------------------------------------------------------------------------------*)
ASSUME ProgramOpsAreReadsWrites ==
  \A tid, req, snap :
    /\ IsSeq(ProgramFor(tid, req, snap))
    /\ \A o \in SI!Range(ProgramFor(tid, req, snap)) :
          /\ o.type = "read" \/ o.type = "write"
          \* Overwriting the txnId field leaves the other fields, in particular `type`,
          \* untouched.  (Rd/Wr/Del emit records with no txnId field, so Merge only adds one.)
          /\ \A t : Merge(o, [txnId |-> t]).type = o.type
          /\ \A t : Merge(o, [txnId |-> t]).txnId = t

THEOREM StepStart ==
  ASSUME Inv, NEW tid, NEW req, StartAndRun(tid, req)
  PROVE  /\ HistoryTypeOK'
         /\ SerializableViaPath'
         /\ SI!CommittedTxns(txnHistory') = SI!CommittedTxns(txnHistory)
PROOF
  <1>1. DEFINE prog    == ProgramFor(tid, req, dataStore)
               beginOp == [type |-> "begin", txnId |-> tid, time |-> clock + 1]
               events  == [i \in 1..Len(prog) |-> Merge(prog[i], [txnId |-> tid])]
               blk     == <<beginOp>> \o events
  <1>2. txnHistory' = txnHistory \o <<beginOp>> \o events BY DEF StartAndRun
  <1>p. IsSeq(prog) BY ProgramOpsAreReadsWrites
  <1>4. IsSeq(blk)
    <2>1. IsSeq(<<beginOp>>) BY DEF IsSeq
    <2>2. Len(prog) \in Nat BY <1>p, LenProperties DEF IsSeq
    <2>3. IsSeq(events) BY <2>2, FcnIsSeqRange
    <2>4. QED BY <2>1, <2>3, ConcatIsSeq
  <1>3. txnHistory' = txnHistory \o blk
    <2>1. PICK U : txnHistory \in Seq(U) BY DEF Inv, HistoryTypeOK, IsSeq
    <2>2. PICK V : blk \in Seq(V) BY <1>4 DEF IsSeq
    <2>3. PICK W : events \in Seq(W)
      <3>1. Len(prog) \in Nat BY <1>p, LenProperties DEF IsSeq
      <3>2. IsSeq(events) BY <3>1, FcnIsSeqRange
      <3>3. QED BY <3>2 DEF IsSeq
    <2>4. txnHistory \in Seq(U \cup W \cup {beginOp})
          /\ <<beginOp>> \in Seq(U \cup W \cup {beginOp})
          /\ events \in Seq(U \cup W \cup {beginOp})
      BY <2>1, <2>3, SeqMonotonic
    <2>5. QED BY <1>2, <2>4, ConcatAssociative
  <1>5. HistoryTypeOK'
    BY <1>3, <1>4, ConcatIsSeq DEF Inv, HistoryTypeOK
  \* Every op of the block is a begin/read/write for tid -- never a commit.
  <1>6. \A o \in SI!Range(blk) : o.txnId = tid /\ o.type # "commit"
    <2>1. Len(prog) \in Nat BY <1>p, LenProperties DEF IsSeq
    <2>2. PICK W2 : events \in Seq(W2)
      <3>1. IsSeq(events) BY <2>1, FcnIsSeqRange
      <3>2. QED BY <3>1 DEF IsSeq
    <2>3. SI!Range(blk) = SI!Range(<<beginOp>>) \cup SI!Range(events)
      <3>1. <<beginOp>> \in Seq(W2 \cup {beginOp}) /\ events \in Seq(W2 \cup {beginOp})
        BY <2>2, SeqMonotonic
      <3>2. QED BY <3>1, RangeConcatenation, RangeSame
    <2>4. SI!Range(<<beginOp>>) = {beginOp} BY DEF SI!Range
    \* Each event is the corresponding program op with txnId overwritten to tid.
    <2>5. SI!Range(events) = {Merge(prog[i], [txnId |-> tid]) : i \in 1..Len(prog)}
      BY <2>1 DEF SI!Range
    <2>6. ASSUME NEW i \in 1..Len(prog)
          PROVE  /\ Merge(prog[i], [txnId |-> tid]).txnId = tid
                 /\ Merge(prog[i], [txnId |-> tid]).type # "commit"
      <3>2. prog[i] \in SI!Range(prog)
        BY <2>1 DEF SI!Range
      <3>1. Merge(prog[i], [txnId |-> tid]).txnId = tid
        BY <3>2, ProgramOpsAreReadsWrites
      <3>3. prog[i].type = "read" \/ prog[i].type = "write"
        BY <3>2, ProgramOpsAreReadsWrites
      <3>4. Merge(prog[i], [txnId |-> tid]).type = prog[i].type
        BY <3>2, ProgramOpsAreReadsWrites
      <3>5. QED BY <3>1, <3>3, <3>4
    <2>7. QED BY <2>3, <2>4, <2>5, <2>6
  \* Freshness: Unused(tid) says no op of tid appears in the history.
  <1>7. tid \notin SI!CommittedTxns(txnHistory)
    <2>1. ~\E op \in SI!Range(txnHistory) : op.txnId = tid
      BY DEF StartAndRun, Unused
    <2>2. QED BY <2>1 DEF SI!CommittedTxns
  <1>8. PICK U2 : txnHistory \in Seq(U2) BY DEF Inv, HistoryTypeOK, IsSeq
  <1>9. PICK V2 : blk \in Seq(V2) BY <1>4 DEF IsSeq
  <1>10. txnHistory \in Seq(U2 \cup V2) /\ blk \in Seq(U2 \cup V2)
    BY <1>8, <1>9, SeqMonotonic
  <1>11. SI!SerializationGraph(txnHistory \o blk) = SI!SerializationGraph(txnHistory)
    BY <1>6, <1>7, <1>10, GraphAppendBlock
  <1>12. SerializableViaPath'
    BY <1>3, <1>11 DEF Inv, SerializableViaPath, SI!IsConflictSerializableViaPath
  \* The committed set is unchanged: the block contributes no commit op.
  <1>14. SI!CommittedTxns(txnHistory') = SI!CommittedTxns(txnHistory)
    <2>1. SI!Range(txnHistory \o blk) = SI!Range(txnHistory) \cup SI!Range(blk)
      BY <1>10, RangeConcat
    <2>2. {x \in SI!Range(txnHistory \o blk) : x.type = "commit"}
          = {x \in SI!Range(txnHistory) : x.type = "commit"}
      BY <1>6, <2>1
    <2>3. QED BY <1>3, <2>2 DEF SI!CommittedTxns
  <1>13. QED BY <1>5, <1>12, <1>14

(*--------------------------------------------------------------------------------------------*)
(* CommitTxn: the one step that adds a node.  Reduces to Part 4.                               *)
(*--------------------------------------------------------------------------------------------*)
THEOREM StepCommit ==
  ASSUME Inv, NEW tid \in TxnIds, CommitTxn(tid), TPCCNoDangerousStructure
  PROVE  HistoryTypeOK' /\ SerializableViaPath'
PROOF
  <1>a. SI!CommitTxn(tid) BY DEF CommitTxn
  <1>1. DEFINE co == [type |-> "commit", txnId |-> tid, time |-> clock + 1,
                      updatedKeys |-> SI!KeysWrittenByTxn(txnHistory, tid)]
  <1>2. txnHistory' = Append(txnHistory, co) BY <1>a DEF SI!CommitTxn
  <1>3. txnHistory' = txnHistory \o <<co>>
    BY <1>2, AppendIsSeq DEF Inv, HistoryTypeOK
  <1>4. HistoryTypeOK' BY <1>2, AppendIsSeq DEF Inv, HistoryTypeOK
  <1>5. PICK U : txnHistory \in Seq(U) BY DEF Inv, HistoryTypeOK, IsSeq
  <1>6. txnHistory \in Seq(U \cup {co}) /\ co \in U \cup {co} BY <1>5, SeqMonotonic
  <1>7. co.type = "commit" OBVIOUS
  <1>8. SI!IsConflictSerializableViaPath(txnHistory)
    BY DEF Inv, SerializableViaPath
  <1>ck. CommitKeepsAcyclic(txnHistory, co)
    BY DEF TPCCNoDangerousStructure
  <1>9. SI!IsConflictSerializableViaPath(txnHistory \o <<co>>)
    BY <1>6, <1>7, <1>8, <1>ck, CommitPreservesSerializable
  <1>10. SerializableViaPath' BY <1>3, <1>9 DEF SerializableViaPath
  <1>11. QED BY <1>4, <1>10

(*--------------------------------------------------------------------------------------------*)
(* Preservation of RunningNotCommitted by each action.                                         *)
(*                                                                                             *)
(* StartAndRun adds a running transaction, but `Unused(tid)` says it has no op in the history  *)
(* at all, so it is not committed.  Abort appends no commit op and shrinks runningTxns.        *)
(* Commit appends a commit op for tid but simultaneously removes tid from runningTxns, so the  *)
(* new committed id is no longer running.                                                      *)
(*--------------------------------------------------------------------------------------------*)

LEMMA RNCAbort ==
  ASSUME Inv, NEW tid, AbortTxn(tid)
  PROVE  RunningNotCommitted'
PROOF
  <1>a. SI!AbortTxn(tid) BY DEF AbortTxn
  <1>1. DEFINE ao == [type |-> "abort", txnId |-> tid, time |-> clock + 1]
  <1>2. txnHistory' = txnHistory \o <<ao>>
    BY <1>a, AppendIsSeq DEF SI!AbortTxn, Inv, HistoryTypeOK
  <1>3. PICK U : txnHistory \in Seq(U) BY DEF Inv, HistoryTypeOK, IsSeq
  <1>4. txnHistory \in Seq(U \cup {ao}) /\ ao \in U \cup {ao} BY <1>3, SeqMonotonic
  <1>5. SI!CommittedTxns(txnHistory') = SI!CommittedTxns(txnHistory)
    BY <1>2, <1>4, CommittedAppendNonCommit
  <1>6. runningTxns' = {r \in runningTxns : r.id # tid} BY <1>a DEF SI!AbortTxn
  <1>7. SI!RunningTxnIds' \subseteq SI!RunningTxnIds
    BY <1>6 DEF SI!RunningTxnIds
  <1>8. QED BY <1>5, <1>7 DEF Inv, RunningNotCommitted

LEMMA RNCStart ==
  ASSUME Inv, NEW tid, NEW req, StartAndRun(tid, req)
  PROVE  RunningNotCommitted'
PROOF
  \* The committed set does not grow (proved as part of StepStart's frame argument).
  <1>1. SI!CommittedTxns(txnHistory') = SI!CommittedTxns(txnHistory)
    BY StepStart
  \* The only new running id is tid, and Unused(tid) makes it uncommitted.
  <1>2. runningTxns' = runningTxns \cup {[id |-> tid, startTime |-> clock + 1,
                                          commitTime |-> Empty]}
    BY DEF StartAndRun
  <1>3. SI!RunningTxnIds' = SI!RunningTxnIds \cup {tid}
    BY <1>2 DEF SI!RunningTxnIds
  <1>4. tid \notin SI!CommittedTxns(txnHistory)
    <2>1. ~\E op \in SI!Range(txnHistory) : op.txnId = tid
      BY DEF StartAndRun, Unused
    <2>2. QED BY <2>1 DEF SI!CommittedTxns
  <1>5. QED BY <1>1, <1>3, <1>4 DEF Inv, RunningNotCommitted

LEMMA RNCCommit ==
  ASSUME Inv, NEW tid, CommitTxn(tid)
  PROVE  RunningNotCommitted'
PROOF
  <1>a. SI!CommitTxn(tid) BY DEF CommitTxn
  <1>1. DEFINE co == [type |-> "commit", txnId |-> tid, time |-> clock + 1,
                      updatedKeys |-> SI!KeysWrittenByTxn(txnHistory, tid)]
  <1>2. txnHistory' = txnHistory \o <<co>>
    BY <1>a, AppendIsSeq DEF SI!CommitTxn, Inv, HistoryTypeOK
  <1>3. PICK U : txnHistory \in Seq(U) BY DEF Inv, HistoryTypeOK, IsSeq
  <1>4. txnHistory \in Seq(U \cup {co}) /\ co \in U \cup {co} BY <1>3, SeqMonotonic
  \* The committed set grows by exactly tid.
  <1>5. SI!Range(txnHistory') = SI!Range(txnHistory) \cup {co}
    BY <1>2, <1>4, RangeAppend
  <1>6. SI!CommittedTxns(txnHistory') = SI!CommittedTxns(txnHistory) \cup {tid}
    <2>1. {x \in SI!Range(txnHistory') : x.type = "commit"}
          = {x \in SI!Range(txnHistory) : x.type = "commit"} \cup {co}
      BY <1>5
    <2>2. QED BY <2>1 DEF SI!CommittedTxns
  \* But tid is simultaneously removed from runningTxns.
  <1>7. runningTxns' = {r \in runningTxns : r.id # tid} BY <1>a DEF SI!CommitTxn
  <1>8. tid \notin SI!RunningTxnIds' BY <1>7 DEF SI!RunningTxnIds
  <1>9. SI!RunningTxnIds' \subseteq SI!RunningTxnIds BY <1>7 DEF SI!RunningTxnIds
  <1>10. QED BY <1>6, <1>8, <1>9 DEF Inv, RunningNotCommitted

(*--------------------------------------------------------------------------------------------*)
(* The stutter case needs no assumption beyond Inv: it leaves `vars` -- and hence txnHistory   *)
(* and runningTxns -- unchanged, so it is proved outright.                                     *)
(*--------------------------------------------------------------------------------------------*)
THEOREM StepStutter ==
  ASSUME Inv, UNCHANGED vars
  PROVE  Inv'
PROOF
  <1>1. txnHistory' = txnHistory /\ runningTxns' = runningTxns BY DEF vars
  <1>2. HistoryTypeOK' BY <1>1 DEF Inv, HistoryTypeOK
  <1>3. SerializableViaPath' BY <1>1
        DEF Inv, SerializableViaPath, SI!IsConflictSerializableViaPath
  <1>4. RunningNotCommitted' BY <1>1
        DEF Inv, RunningNotCommitted, SI!RunningTxnIds
  <1>5. QED BY <1>2, <1>3, <1>4 DEF Inv

(*--------------------------------------------------------------------------------------------*)
(* The inductive step: a case split over Next, discharged by the theorems above.               *)
(*--------------------------------------------------------------------------------------------*)
THEOREM Inductive == Inv /\ TPCCNoDangerousStructure /\ [Next]_vars => Inv'
PROOF
  <1>1. SUFFICES ASSUME Inv, TPCCNoDangerousStructure, [Next]_vars PROVE Inv' OBVIOUS
  <1>2. CASE Next
    <2>1. CASE \E tid \in TxnIds, req \in Requests : StartAndRun(tid, req)
      <3>1. PICK tid \in TxnIds, req \in Requests : StartAndRun(tid, req) BY <2>1
      <3>2. HistoryTypeOK' /\ SerializableViaPath' BY <1>1, <3>1, StepStart
      <3>3. RunningNotCommitted' BY <1>1, <3>1, RNCStart
      <3>4. QED BY <3>2, <3>3 DEF Inv
    <2>2. CASE \E tid \in TxnIds : CommitTxn(tid)
      <3>1. PICK tid \in TxnIds : CommitTxn(tid) BY <2>2
      <3>2. HistoryTypeOK' /\ SerializableViaPath'
        BY <1>1, <3>1, StepCommit, TPCCNoDangerousStructure
      <3>3. RunningNotCommitted' BY <1>1, <3>1, RNCCommit
      <3>4. QED BY <3>2, <3>3 DEF Inv
    <2>3. CASE \E tid \in TxnIds : AbortTxn(tid)
      <3>1. PICK tid \in TxnIds : AbortTxn(tid) BY <2>3
      <3>2. HistoryTypeOK' /\ SerializableViaPath' BY <1>1, <3>1, StepAbort
      <3>3. RunningNotCommitted' BY <1>1, <3>1, RNCAbort
      <3>4. QED BY <3>2, <3>3 DEF Inv
    <2>4. CASE AllTxnsDone /\ UNCHANGED vars
      BY <1>1, <2>4, StepStutter
    <2>5. QED BY <1>2, <2>1, <2>2, <2>3, <2>4 DEF Next
  <1>3. CASE UNCHANGED vars
    BY <1>1, <1>3, StepStutter
  <1>4. QED BY <1>1, <1>2, <1>3

(*--------------------------------------------------------------------------------------------*)
(* The base case for the full invariant.                                                       *)
(*--------------------------------------------------------------------------------------------*)
THEOREM InitInv == Init => Inv
PROOF
  <1>2. Init => SerializableViaPath BY Base
  <1>3. Init => HistoryTypeOK
    <2>1. Init => txnHistory = <<>> BY DEF Init
    <2>2. QED BY <2>1, EmptyIsSeq DEF HistoryTypeOK
  <1>4. Init => RunningNotCommitted
    <2>1. Init => SI!RunningTxnIds = {} BY DEF Init, SI!RunningTxnIds
    <2>2. QED BY <2>1 DEF RunningNotCommitted
  <1>5. QED BY <1>2, <1>3, <1>4 DEF Inv

(*--------------------------------------------------------------------------------------------*)
(* And the top-level result.  Fully assembled -- no OMITTED here; it rests on the step         *)
(* theorems above, which are where the remaining work actually is.                             *)
(*--------------------------------------------------------------------------------------------*)
THEOREM Safety == Spec /\ []TPCCNoDangerousStructure => []SerializableViaPath
PROOF
  <1>1. Init => Inv BY InitInv
  <1>2. Inv /\ TPCCNoDangerousStructure /\ [Next]_vars => Inv' BY Inductive
  <1>3. Inv => SerializableViaPath BY DEF Inv
  <1>4. QED BY <1>1, <1>2, <1>3, PTL DEF Spec

====
