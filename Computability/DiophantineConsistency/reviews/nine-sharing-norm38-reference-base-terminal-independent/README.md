# Independent terminal review of concrete reference topology

The first two post-hoc author records report sessions **42729** and **35832**
exiting 1. Both dependency scans passed, but Lean could not synthesize a
`Decidable` instance: first for the recursive topology predicate, then for
the unfolded long conjunction. Both failed logs include `sorryAx` in the
attempted axiom print and do not prove the theorem.

The third author-recorded session **51506 exited 0**. Its source preserves
the reference definition and exact theorem statement; it first unfolds the
finite predicate, then splits conjunctions before deciding the individual
goals. Its compiled `graph_topological` theorem asserts that the actual 60
static gates are topologically ordered after the designated 21 initial nodes.
The same object contains the 81-node reference definition, but does not prove
that reference satisfies the gate equations or matches the Carrier65 fields.
The successful axiom report is exactly `[propext, Classical.choice, Quot.sound]`.
The object remains in `/tmp/nine-sharing-norm38-reference-base-retry02-20261105/`
with SHA-256 `723434d993b01cc17c86d82fc0eba7bf9a7723913dc879405666631c15b265f5`.

`check.py` verifies all three source snapshots and exact proof deltas, retained
dependency/compile logs, the successful object and axiom report, the common
compiled `SharingTopology38` provider, 100 direct guard slots and 1,066
overlay links per attempt. It also reruns the separate external 60-row graph
mapping check. Failed runs did not reach success-path final guards; this
review checks their recorded pre-compile guards against current files.

The outer exits are author records, not raw transcripts or independently
observed historical exits. No Lean process was run during this review.
Inherited package/dynamic ancestry, between-observation changes and sampled
resource limits remain. No source-graph theorem, model bridge or iPRA endpoint
follows from this topology check alone.
