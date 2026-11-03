# Captured-header plan for 28 graph-support sources

This is a **read-only plan**, not a replay. `check.py` pins the final selected
header graph, [28-object triage](../trace75-graph-support-28-triage/README.md),
the [seven structured observations](../trace75-graph-support-seven-observations/README.md)
and the separate [packing-blocks observation](../trace75-packing-blocks-observation/README.md).
It verifies current candidate source hashes and declared imports, checks the
captured direct input objects and companions, and emits a deterministic
topological order in attempt01 stdout. It invokes no Lean and does not alter
the selected provider.

The captured 28-node graph has **9 internal dependency edges**, **31 unique
direct project inputs outside the subset**, and one direct outside name,
`Init`. All 28 sources are available at the scanned paths: 27 match the
same-named overlay-root source and a workspace prototype byte-for-byte; the
packing-blocks source is the retained source from its reported session, with
no same-named overlay-root source. Source/hash matches do not authenticate
the selected output's producer. Eight sources have separate reported
successful source-session observations, with the non-atomic and direct-input
limitations documented in the two observation packets. The other 20 do not
gain such a claim from this plan.

The 27 overlay-matched sources contain 60 literal `#print axioms` directives;
`ArithmeticPackingBlocks` contains none. The source tokens are listed per
stage, but their elaborated report names and acceptable outputs must be
verified when preparing a runner. The earlier triage found 22 names with
same-name overlay logs; their filenames are candidates, not authenticated
stage-output expectations. Any warning policy must be explicit and grounded
in reviewed evidence; do not silently accept them or treat empty output as a
proof of a historical exit.

To attempt the subset replay, wait for a reviewed runner that pins all 28
source bytes, the exact parent result and actual outer exit, and the 31
direct selected project bundles and `Init` bundle. Construct a private
merged `DiophantineConsistency` namespace, remove only the 28 selected
output bundles from the private copy, and build in the emitted order. Check
each first-selected direct import and companions before and after its stage,
capture source snapshots, actual exits, warnings and applicable axiom
reports, and never mutate the parent provider. An independent result audit
and a separate paired replay are further work.

This 28-node build alone would **not** authenticate the final endpoint.
Reverse reachability from these nodes in the captured fixed-endpoint graph
contains **331 project modules including the 28**. Rebuilding dependent
objects would require its own source/receipt inventory, compatible
first-selections and an expanded plan. The 31 upstream project inputs,
package-transitive and dynamically loaded inputs, and potentially changed
source imports remain additional boundaries. Equal output bytes would not
alone authenticate historical producer selection; external JSON/TeX/PDF
binding and an independent Lean replay remain separate.

Author attempt01 exited 0. Checker SHA-256 is
`6e0ca8bc7e27bed88ef29a890819ae506ba935abf372e406a7ba4ea68b349301`,
terminal SHA-256 is
`e2dc258cc13d7b31da2a9a9a4388d75ab5ab0ed6ca14b9a178ea08825511b518`,
and stdout SHA-256 is
`a6293d79952afa80ce14d558eb2e363795c1ffff9dc3d0898c23ff3f1ccf04da`.
Independent audit: [`reviews/trace75-graph-support-replay-plan-independent/README.md`](../../reviews/trace75-graph-support-replay-plan-independent/README.md) (SHA-256 `95786fdd2b3eda320864a0653402191782eb47749943dd154de7701acdd3186b`). The audit retains the 331-node captured impact and does not authenticate source-to-object producer linkage.
