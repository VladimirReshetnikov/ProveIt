# Generic proof of exact packed-table binding

[`ControlTableBinding`](../../../../Lean/BusyBeaver/ZFC/ControlTableBinding.lean)
proves that successful checks at every decoder leaf, together with an exact
row-count equality, imply equality of the entire packed table and the source
catalogue. The test compares the opcode, physical register and **both stored
successor fields**, including the unused second field of non-test rows.

The executable check uses cached subtree counts. Its soundness requires the
counted tree to equal `ControlCatalogue.annotate` of the source tree. Complete
path enumeration and absence of duplicates prove that each path rank names
its exact list entry. Further theorems resolve arbitrary outgoing paths to the
consumed leaf path, including implicit zero extension. No default or unrelated
source entry is substituted for an unresolved path.

The [actual check](../../results/w6-control-table-binding-verification.json)
passes six axiom probes and nine typed callers with zero warnings and only
standard Lean axioms. Source/audit times were 1.767/1.517 seconds under default
proof limits, sharing 120 seconds, one thread and 4,096 MiB. The guard selects
36 project prerequisites, three external boundaries and Init/Omega from the
completed table-interpreter and packed-table checks. Existing dependency
caches are reused without rebuilding or whole-cache attestation.

The original draft needed explicit qualification of `ControlCatalogue.CTree`.
Two actual attempts then exposed indexing-notation and existential-binder
parsing issues under the arithmetic imports. The accepted version uses
explicit `getElem`/`getElem?` applications and separate existential binders.
All original drafts, failed logs and the final source/audit are preserved in
the [history](history.json.gz); the [publication record](../../results/w6-control-table-binding-publication.json)
identifies the accepted execution. These records retain historical scratch
paths. Source review is supplementary to the actual compiler evidence.

The [completed-run review](review.json) confirms that the final source retains
the original proof hypotheses and conclusions and that the raw logs, providers
and fresh-object captures agree. It discloses the reviewer's guard authorship;
its [reader and history](review-history.json.gz) are retained separately.

This theorem is generic and conditional on a complete row check. The
[counted tree](../counted-tree/README.md) discharges the annotation premise for
Rotation240. The [complete concrete check](../table-rows/README.md) now proves
the 6,455-row acceptance and resulting exact table equality. The internal
binary simulation and PA endpoint remain open. The construction reuses the maintained catalogue, decoder
and physical-register mapping, with their original attribution.
