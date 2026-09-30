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

## Limits

- Bounded instances only. 3 transactions, 1 warehouse, 2 districts. The 1.31M-state run is
  exhaustive *for those parameters*; it is not a proof for TPC-C in general.
- The Order-Status index approximation above.
- Conflict serializability, not view serializability — the former is strictly stronger, so
  the verdict is sound in the safe direction.
- Aborts are modelled only as First-Committer-Wins write conflicts, matching the SI module.
  No client-initiated rollback (TPC-C's 1% New-Order rollback is not represented).
