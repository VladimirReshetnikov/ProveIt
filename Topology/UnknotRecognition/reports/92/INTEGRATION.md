# Integration contract

## Start with the research modules, not a recognizer replacement

Keep this delivery isolated under its report directory. The current native raw-cut APIs inspected in the repository are `normal_cut_cell_complex` and `verify_normal_cut_cell_complex`, with schema `normal-cut-cells-v1`. No import adapter to those APIs is delivered here. The mathematical caller contract is broader than their inspected source domain; later pieces require separate validation.

A safe first integration is a read-only research observer that exports a chamber graph, authenticates it, and compares selected batches. It should not alter verdicts or production dispatch.

## Native source exporter: required output

The native exporter must establish all of the following in a common authenticated source:

1. A list of connected, properly embedded, pairwise disjoint, two-sided/cooriented candidate surface components. Explicit labels matter. Compatible normal coordinate vectors alone do not establish the required labeled coembedding.
2. A compressed relation on raw atomic chambers whose orbits are exactly global full-cut chambers. It includes original-face adjacency and excludes crossings through the candidate surfaces.
3. One authenticated atom on each global side of each candidate. A connected side belongs to one chamber. One-sided or disconnected candidates must be rejected or handled by a separate proven interface.
4. The weighted-orbit proof for scalar marker weights `2**j`. Markers aliasing the same atom must have their weights added.
5. A source identity and explicit maps binding the markers and the relation to the actual source packet.

The graph decoder checks only the census's algebraic consistency. Passing its checks is not source authentication.

## Graph API

Add the delivered `code/` directory to the import path. A graph-level example is:

```python
from cographic import decode_side_census, maximum_batch
from verify import verify_batch

# Side markers 0,1,3 share a chamber; marker 2 is in another.
graph = decode_side_census(2, [(11, 1), (4, 1)], weights=[7, 1])
packet = maximum_batch(graph)
assert verify_batch(packet)
```

`maximum_batch` returns the complement of an optimal connecting tree. Selected edges represent the retained/cut candidates. Tree edges are the candidates left uncut for this batch. Do not reverse those roles.

## Composite optimizer

The new composite entry point prices retained progress by its downstream path amplification:

```python
from reuse import plan_reuse
from verify import verify_reuse

packet = plan_reuse(
    vertices=3,
    edges=[(0, 1), (1, 2), (0, 2)],
    caps=[1, 1, 1],
    parents=[[], [0], [1]],
    saved=[1, 1, 1],
)
assert verify_reuse(packet)
assert packet['baseline_work_bound'] == 11
assert packet['retained_work_bound'] == 4
assert packet['batch']['chosen'] == [0]
```

Candidate IDs map injectively to task IDs; the default mapping is the identity. Optional `tasks` gives a different injection, and `costs` provides one nonnegative integer per-event cost bound per task. Noncandidate tasks begin at their caps. Dependencies, caps, and event costs must stay fixed across the batches being compared.

The independent verifier recomputes the amplification, graph rewards, initial budgets, tree certificate, and forward work bounds. It does not authenticate the source geometry, prove that a dependency edge is sufficient, or validate the claimed saved progress as a geometric fact.

## Dual-route exporter: still required

For each retained candidate, export a loop crossing it once and avoiding all other retained candidates. The loop needs a source-interpretable grammar and an independent checker. The finite `finite_routing_forest` is a reference for a fully explicit arena, not a binary native route construction. A forest with one record per represented normal copy can be exponentially large.

A usable route certificate must expose a conservative support for every source record it reads. Include surfaces, loops, sides, orientation frames, attaching maps, source charts, and any boundary facts used in checking them. A surface-only support can miss a destroyed return path.

Graph-level shared routes are not necessarily disjoint embedded curves until a geometric lift and disjointification have been authenticated. The existence theorem is not an implementation of that process.

## Versions and transactions

Task IDs must be topological. Initially snapshots are valid. A repair strictly lowers a nonnegative integer potential and changes a version. A rebuild is legal only after a new direct-parent snapshot and with valid parents; it changes a version and restores potential to at most its cap. A zero-cap task can still rebuild.

For a transaction, verify source identity, chamber proof, selected batch, dual routes, edit footprint, and geometric transport before committing the new snapshot. Abandoned or timed-out work must not produce a usable partial result. Retain the old state or mark genuinely affected tasks stale.

A local one-crossing certificate proves nonseparation only. It does not transport incompressibility, essential boundary patterns, admissibility, normal form, or a claim that a sphere boundary bounds a ball. Those obligations require separate proof objects or theorems and dependencies.

## Metrics to record in native experiments

Record actual versions and rebuilds, source-epoch count, candidate count, source and grammar bit lengths, numerical potential caps, maximum dependency depth, invalidation-set sizes, source verification time, route cost, retained work, failed attempts, and fallback time. Compare identical full calls with paired order and controls. Do not report the local exhaustive-reference ratio in this delivery as a production or recognition speedup.

## Intake catalog text

Cographic persistence, one-census chamber graphs, local dual-loop certificates, a fixed-DAG reset path bound, and downstream-amplified optimal reuse. Includes independent finite verifiers and recorded checks. General quasi-polynomial recognition and native source integration remain explicit obligations.

## Optional online amortized ledger

`causal.causal_potential(caps, parents, remaining, versions, snapshots, costs=None)` computes the proved nonnegative potential, including counts of unobserved parent versions. Each legal event decreases it by at least its charged event cost. A change of dependency arena can increase it; the positive increase is a separately recorded potential injection. Computing, authenticating, and applying source/arena changes has its own cost and must not be hidden in that accounting. This is an alternative quantitative research target, not a waiver of source validity or global hierarchy obligations.
