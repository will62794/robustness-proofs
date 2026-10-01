# TPC-C under Snapshot Isolation, in TLA+

A TLA+ model of a TPC-C workload running on a key-value store that provides
**snapshot isolation**, built so that TLC can answer:

> Is every history this workload produces conflict serializable?

The snapshot isolation layer is not reimplemented here. `SnapshotIsolation.tla` is
[will62794/snapshot-isolation-spec](https://github.com/will62794/snapshot-isolation-spec)
verbatim; `TPCC.tla` `INSTANCE`s it. Begin snapshots, read-your-own-writes,
First-Committer-Wins, and the multi-version serialization graph all come from that module.
This repo only adds the *workload* — which items each transaction touches, and in what order.

## The headline result

**Conflict granularity is not an implementation detail. It decides the answer.**

| Model | Result |
|---|---|
| Column granularity, New-Order + Payment + Stock-Level, 3 txns | **serializable** — exhaustive, 1.31M distinct states, no error |
| Row granularity, same parameters | **VIOLATED** — cycle found in ~1 min |

Fekete, Liarokapis, O'Neil, O'Neil & Shasha, *Making Snapshot Isolation Serializable*
(TODS 2005, §5) show TPC-C is serializable under SI because its static dependency graph has
no "dangerous structure" — no two consecutive read-write anti-dependency edges. That analysis
is carried out **per attribute**. It does not survive coarsening to rows, and most real SI
engines detect conflicts per row.

The counterexample TLC finds (`logs/row-3txn.log`):

```
T1  NewOrder(w1, d1, c1, {i1})            begin@1  commit@5
T2  Payment(w1, d2, customer w1/d1/c1)    begin@2  commit@3
T3  StockLevel(w1, d2)                    begin@4  commit@6

T1 --rw--> T2    T1 read W_TAX,       T2 wrote W_YTD        [begin(T1)=1 < commit(T2)=3]
T2 --wr--> T3    T2 wrote D_YTD,      T3 read D_NEXT_O_ID   [commit(T2)=3 < begin(T3)=4]
T3 --rw--> T1    T3 read S_QUANTITY,  T1 wrote S_QUANTITY   [begin(T3)=4 < commit(T1)=5]
```

Only the third edge is real. The first two are false conflicts manufactured by row
granularity: New-Order and Payment share the WAREHOUSE *row* but no column, and Payment and
Stock-Level share the DISTRICT row but no column. Each false edge is individually harmless;
together they close a cycle. The trace even exhibits the dangerous structure
(`T3 --rw--> T1 --rw--> T2`), which is exactly the precondition the paper's argument rules out.

Flip `ColumnGranularity` in the config to reproduce either side.

## Running it

```bash
./mk.sh col-3txn      # main result: serializable, exhaustive  (~14 min, 8 workers)
./mk.sh row-3txn      # counterexample                         (~1 min)
./mk.sh col-allmix    # all five transaction profiles
```

Logs land in `logs/`. `mk.sh` expects `tla2tools.jar` at `~/tla2tools.jar`.

## What is modelled

All five TPC-C profiles: New-Order, Payment, Order-Status, Delivery, Stock-Level.
`EnabledTxnTypes` selects the mix; scale factors (warehouses, districts, customers, items,
orders, transactions) are all constants. Realistic instances are far out of reach — these are
1 warehouse, 2 districts, 3 transactions — so this is a bounded check, not a proof.

Three modelling decisions carry the weight.

### 1. Predicate reads are range scans

Delivery ("lowest undelivered order"), Order-Status ("this customer's last order") and
Stock-Level ("the last 20 orders") select rows by predicate, not by key. Recording only the
rows that *matched* would silently drop phantom anti-dependencies: a concurrent insert that
would have matched is a genuine read-write conflict but leaves no trace in the matching set.
So each predicate reads every key in its range, present or absent — sound, and what a real
engine without predicate locking does.

One spot is conservative rather than exact: Order-Status scans the whole district ORDER range
instead of probing the `(o_w_id, o_d_id, o_c_id)` index, so it sees other customers' orders.
That can only *add* rw-edges, never remove them, so a "serializable" verdict stays valid — but
a violation found in a mix including Order-Status would need checking against this.

### 2. Transaction bodies collapse into one step, and that is exact

`Next` runs a whole transaction body in a single step between begin and commit. This is not an
approximation. Under SI a transaction's reads come entirely from its begin snapshot plus its
own writes, and its writes are invisible until commit — so where a body operation sits inside
`[begin, commit]` is unobservable to everyone else. The MVSG is built only from begin times,
commit times, and per-transaction read/write key sets, never from body interleaving. The set
of reachable MVSGs is therefore identical under either granularity.

The argument has one premise that is easy to get wrong, so it is checked rather than asserted:
no TPC-C transaction reads an item it has already written (invariant `NoReadAfterWrite`). A
second check, `NoDuplicateOps`, confirms each transaction touches any given item at most once
per operation type, so a collapsed body is still a legal SI execution.

### 3. Values are dropped unless they steer control flow

Conflict serializability depends on the access pattern, not the data. Only four stored values
decide *which items get touched* — `D_NEXT_O_ID`, NEW-ORDER row existence, `O_C_ID`, and
`OL_I_ID`. Everything else is written by exactly the transactions TPC-C says write it, but
stores a constant tag. This removes no MVSG edge and keeps the state space finite.

Two aggregations, both exact: all order lines of an order are one item (every TPC-C statement
touches them together), and each Payment's HISTORY row is its own key (HISTORY is insert-only
with a fresh row per transaction, so it can never conflict).

## Invariants

**Correctness**

- `Serializable` — the main question; MVSG over committed transactions is acyclic.
- `NoDangerousStructure` — strictly stronger, and the *reason* `Serializable` holds: no two
  consecutive rw-anti-dependency edges. This is the machine-checked form of the paper's
  static argument.
- `NoReadOnlyAnomaly` — the Fekete/O'Neil/O'Neil read-only anomaly.

**Model validity** (these justify the simplifications above)

- `NoReadAfterWrite` — justifies collapsing transaction bodies.
- `NoDuplicateOps` — the SI module's `TxnRead`/`TxnUpdate` are guarded against repeating a
  key; this confirms each collapsed body touches any given item at most once per operation
  type, so it stays within what those actions would permit.
- `OrderIdsContiguous` — TPC-C Consistency Condition 3 in spirit: an order exists iff its id
  is below the district's `D_NEXT_O_ID`.

**Coverage** — meant to *fail*. A passing run here means the model is too small to be saying
anything, and `Serializable` holds only vacuously. Each is checked as a separate run:

`Cov_AllTxnsCommit`, `Cov_SomeTxnAborts`, `Cov_ConcurrentTxns`, `Cov_RWEdgeExists`
(`Cov_RWEdgeExists` is the important one: no rw-edge means no possible anomaly).

## A machine-checked proof: `Auction_Proofs.tla`

Everything above is bounded model checking. `Auction_Proofs.tla` is a complete TLAPS proof of

```
THEOREM Safety == Spec => []SerializableViaPath
```

for `Auction.tla`, under one explicit assumption:

```
ASSUME RobustMix == EnabledTxnTypes \subseteq {"StoreBid", "ViewItem"}
```

This is unbounded in every parameter — any number of items, users, and transactions — unlike
the TLC runs, which fix 2 items and 3 transactions.

The assumption is necessary, not a convenience. `RegUser` genuinely violates the property
(`configs/auction-reguser.cfg` finds the Figure 2(d) write skew in under a second), so no
proof of the unrestricted statement exists.

```bash
tlapm Auction_Proofs.tla      # 1041 obligations, no OMITTED steps
```

### The argument

Fekete et al. rule out the "dangerous structure" — two consecutive rw-anti-dependency edges
around a cycle. For this workload there is a more direct argument that avoids reasoning about
cycles entirely: the MVSG carries a strictly increasing integer rank, so it is acyclic.

```
rank(t) == IF t writes anything THEN commit(t) ELSE begin(t)
```

Updaters are ranked by commit time, read-only transactions by begin time. Three properties of
the history make every edge increase this rank:

| | property | source |
|---|---|---|
| H1 | `begin(t) < commit(t)` | the clock ticks on both events |
| H2 | a transaction that writes reads only keys it also writes | **the workload** |
| H3 | two committed transactions writing a common key have disjoint lifetimes | First-Committer-Wins |

The ww and wr cases are immediate. The rw case is the one write skew rides on, and it splits:

- `t1` read-only — `rank(t1) = begin(t1) < commit(t2) = rank(t2)` directly from the edge.
- `t1` an updater — `t1` read the key `t2` wrote, so by H2 it *wrote* that key too. Now H3
  applies: the two have disjoint lifetimes, and the edge rules out `t2` finishing first, so
  `commit(t1) =< begin(t2)`. The anti-dependency has been upgraded to a ww-style ordering.

That last case is where robustness lives. An rw edge out of an updater is never really an
anti-dependency here — First-Committer-Wins has already serialized the pair. Only read-only
transactions emit genuine anti-dependency edges, and they have no outgoing ww or wr edges, so
no cycle can close through one.

H2 is the only clause that mentions the auction programs, and it is exactly what separates the
two sides of the paper's analysis:

- `StoreBid(i)` reads `ITEM(i)` and writes `ITEM(i)`. Its one read is of a key it writes. (The
  `BIDS` insert uses a fresh key nobody reads.)
- `ViewItem(i)` writes nothing, so the implication is vacuous.
- `RegUser` **violates it**: it scans every `USERS` key but writes one. A predicate read with
  no matching write is precisely the shape H2 forbids, and precisely why the transaction is not
  robust.

Because the two enabled programs have length 3 and 1, their operations are enumerated
literally in the proof, so none of `ConcatOver` / `Flatten` / `SeqOf` has to be reasoned about.
`RegUser` and `ViewUsers`, which do scan via `ConcatOver`, are excluded by `RobustMix`.

### Structure

| Part | Content |
|---|---|
| 1 | base case: the empty history is serializable |
| 2 | generic: a graph with a strictly increasing rank has no cycle |
| 3 | H1–H3 make every MVSG edge increase the rank |
| 4 | the workload lemma: the auction programs satisfy H2 |
| 5–7 | sequence infrastructure, stability lemmas, the body block `StartAndRun` appends |
| 8–9 | the inductive invariant, and its conversion to H1–H3 |
| 10–13 | initial state and the three actions (`StartAndRun`, `AbortTxn`, `CommitTxn`) |
| 14 | assembly |

Two notes on how the invariant is set up, both of which keep the proof tractable:

- It carries `\E S : txnHistory \in Seq(S)` rather than a precise operation type. Every
  ingredient of the graph reads the history only through its *range*, so "is a sequence" is all
  that is needed, and no reasoning about the value domain of reads and writes is required. The
  corresponding TPC-C development stalls on exactly this point.
- Clauses are stated over the range of the history rather than over `SI!BeginOp` / `SI!CommitOp`.
  Those two are `CHOOSE`s, and a `CHOOSE` over a growing set needs a uniqueness argument at
  every step; quantifying over operations instead and converting once, at the end, keeps that
  reasoning in one place.

## A machine-checked proof for TPC-C: `TPCC_Proofs.tla`

`TPCC_Proofs.tla` is a complete TLAPS proof of

```
THEOREM Safety == Spec => []SerializableViaPath
```

for `TPCC.tla`, under two explicit assumptions:

```
ASSUME ColGran   == ColumnGranularity = TRUE
ASSUME RobustMix == EnabledTxnTypes \subseteq {"NewOrder","Payment","OrderStatus","StockLevel"}
```

Unbounded in every scale factor — any number of warehouses, districts, customers, items,
orders and transactions — unlike the TLC runs above, which fix 1 warehouse and 3 transactions.

```bash
tlapm TPCC_Proofs.tla      # 1275 obligations, no OMITTED steps
```

(The TLC side of this comparison is `configs/row-3txn.cfg` and `configs/col-delivery.cfg`,
both of which check `SerializableViaPath`. The older TPC-C configs — `col-3txn`, `col-allmix`
and the `cov-*` set — still name `Serializable`, `NoReadAfterWrite`, `NoDuplicateOps`,
`OrderIdsContiguous` and `NoDangerousStructure`, which the current `TPCC.tla` no longer
defines; TLC rejects them at parse time until they are updated.)

### The argument

Same rank-function shape as the auction proof: the MVSG carries a strictly increasing integer
rank, so it is acyclic.

```
rank(t) == IF t writes anything THEN commit(t) ELSE begin(t)
```

Four properties of the history make every edge increase it:

| | property | source |
|---|---|---|
| H1 | `begin(t) < commit(t)` | the clock ticks on both events |
| H2 | a committed transaction never writes a read-only column group | **the workload** |
| H3 | an updater reads a *writable* key only if it also writes it | **the workload** |
| H4 | two committed transactions writing a common key have disjoint lifetimes | First-Committer-Wins |

H3 is the clause write skew would ride on, and it needs relativising for TPC-C in a way the
auction did not. New-Order reads `W_TAX`, `D_TAX`, `CUSTOMER.info` and `ITEM.info` without
writing them, so the plain "updaters read only what they write" is false here. Those four
column groups are read-only for the entire benchmark (`ReadOnlyKey` in the proof), and a read
of a key nobody writes emits no rw-edge, so excluding them costs nothing. H2 is what makes
that exclusion sound: it says no committed transaction ever writes one of those groups, so
`ReadOnlyKey` really is read-only rather than merely read-only-so-far.

With H3 in hand the rw case splits exactly as in the auction proof — a read-only `t1` gives
`begin(t1) < commit(t2)` directly from the edge, and an updating `t1` must also have written
the key, so H4 upgrades the anti-dependency to a commit-order edge. Only read-only
transactions emit genuine anti-dependency edges, and they have no outgoing ww or wr edges.

### Why each assumption is needed

The two assumptions have different status, and it is worth being precise about which.

**`ColGran` is necessary.** Under row granularity `W_TAX` and `W_YTD` collapse into one
WAREHOUSE key that New-Order reads and Payment writes. `ReadOnlyKey` has nothing left to
exempt, and H3 fails for New-Order. This is not an artifact of the argument:
`configs/row-3txn.cfg` is a genuine counterexample to `SerializableViaPath` itself, so no proof
of the unrestricted statement exists.

**`RobustMix` is a limit of this argument, with the question left open.** Delivery breaks H3: it
reads `ORDER.hdr` and `ORDERLINE.items` — both written by New-Order, so neither is a
`ReadOnlyKey` — without writing either. Its writes go to `NEWORDER.row`, `ORDER.carrier`,
`ORDERLINE.delivery` and `CUSTOMER.balance`, a disjoint set. So Delivery is an updater emitting
real anti-dependency edges, which is exactly the shape the rank function cannot absorb.

Unlike the row-granularity case, that does *not* come with a counterexample. TLC on
`configs/col-delivery.cfg` (New-Order + Delivery, 3 txns) finds **no error** in 162,565 distinct
states. So whether TPC-C including Delivery is serializable under column-granularity SI is
open as far as this development goes — the rank function is simply the wrong proof technique
for it, and a proof would need the cycle-based dangerous-structure argument the rank function
was chosen to avoid.

The other three profiles go through directly: Payment reads `W_YTD`, `D_YTD` and `C_BALANCE`
and writes all three; Order-Status and Stock-Level write nothing, making H2 and H3 vacuous.

### Structure

| Part | Content |
|---|---|
| 1 | base case: the empty history is serializable |
| 2 | generic: a graph with a strictly increasing rank has no cycle |
| 3 | H1–H4 make every MVSG edge increase the rank |
| 4 | the workload lemma: the four enabled profiles satisfy H2 and H3 |
| 5–6 | sequence infrastructure, and the inductive invariant |
| 7 | converting the invariant to H1–H4 |
| 8–11 | initial state and the four actions |
| 12 | assembly |

As in the auction proof, the invariant carries `\E S : txnHistory \in Seq(S)` rather than a
precise operation type, and states its clauses over the *range* of the history rather than
through `BeginOp` / `CommitOp`. Those two are `CHOOSE`s; quantifying over operations instead
and converting once, in Part 7, keeps the uniqueness reasoning in one place.

One thing made this tractable that the earlier TPC-C attempt lacked: because `TPCC.tla` records
a transaction body as a *single* event carrying its read and write key sets, the workload lemma
is pure set reasoning over `RdKeys` / `WrOps`, with no recursive sequence-concatenation
operator to unfold.

## SmallBank: `SmallBank.tla`

The SmallBank benchmark (Alomari, Cahill, Fekete & Röhm, ICDE 2008), with the same structure as
`TPCC.tla` and `Auction.tla`: it `INSTANCE`s `SnapshotIsolation` and supplies only the five
programs — Balance, DepositChecking, TransactSavings, Amalgamate, WriteCheck — as read/write
key sets over `ACCOUNT`, `SAVINGS` and `CHECKING`.

No stored value steers which keys a SmallBank program touches (every access is by primary key),
so balances are abstracted to a constant tag, as TPCC does for its non-steering columns. As a
result, balance-dependent client rollbacks aren't modelled.

| Config | Mix | Result |
|---|---|---|
| `smallbank-robust` | all but WriteCheck, 2 customers, 3 txns | **serializable**: 116,401 distinct states, no error |
| `smallbank-nobalance` | all but Balance, 2 customers, 3 txns | **serializable**: 116,401 distinct states, no error |
| `smallbank-roanomaly` | Balance + WriteCheck + TransactSavings, 1 customer | **VIOLATED** in 3s |
| `smallbank-allmix` | all five, 2 customers, 3 txns | **VIOLATED** in 24s |

In both robust runs `Cov_RWEdgeExists`, `Cov_SomeTxnAborts` and `Cov_AllTxnsCommit` fail as
expected, so neither result is vacuous.

The counterexample is the Fekete/O'Neil/O'Neil read-only anomaly, with WriteCheck as the pivot:

```
T1  WriteCheck(c1)        begin@1  commit@5
T2  TransactSavings(c1)   begin@2  commit@3
T3  Balance(c1)           begin@4  commit@6

T1 --rw--> T2    T1 read SAVINGS,   T2 wrote SAVINGS
T2 --wr--> T3    T2 wrote SAVINGS,  T3 read SAVINGS
T3 --rw--> T1    T3 read CHECKING,  T1 wrote CHECKING
```

WriteCheck is the only updater that reads a key it doesn't write (`SAVINGS`). So under the
rank-function argument used in the proofs above, H2/H3 hold for every mix without WriteCheck.
Leaving out Balance is also enough. WriteCheck's anti-dependency edges are then never preceded
by another one, because every program that writes `CHECKING` also reads it.

`mk.sh` hardcodes the `TPCC` module, so run these configs directly:

```bash
java -cp tla2tools.jar tlc2.TLC -workers 8 -config configs/smallbank-roanomaly.cfg SmallBank
```

## Limits

- Bounded instances only. 3 transactions, 1 warehouse, 2 districts. The 1.31M-state run is
  exhaustive *for those parameters*; it is not a proof for TPC-C in general.
- The Order-Status index approximation above.
- Conflict serializability, not view serializability — the former is strictly stronger, so
  the verdict is sound in the safe direction.
- Aborts are modelled only as First-Committer-Wins write conflicts, matching the SI module.
  No client-initiated rollback (TPC-C's 1% New-Order rollback is not represented).
- The TLAPS proof assumes the robust mix. The unrestricted statement is false, so this is a
  limit of the theorem rather than of the proof.
