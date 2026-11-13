# Producer records at the 40 peer-overlay boundaries

All **40** missing-record boundaries in the pinned preceding trace now match a
successful record in the retained state of the **selected physical object
provider**, by logical module name and exact object SHA-256. For each, the
checker also rehashes the selected object, the producer state, its source
snapshot and compiler log, using the prior source-origin audit to bind the
snapshot and log to that provider record. Where the producer row itself records
a source hash, the source-origin hash is checked against it.

Recursively following selected project imports through these three provider
states reaches **172** objects, including the original 40, with **259**
recorded `DiophantineConsistency` edges. All 259 selected object hashes match
the respective producer records; no selected-owner row is missing. One edge
returns to an object recorded in the earlier trace. All 172 selected physical
objects, source snapshots and logs match the prior source-origin inventory and
are rehashed by this checker. Their selected provider distribution is:

* 139 from `/tmp/pra14-full-transitive-g3ull6n_`;
* 27 from `/tmp/ipra-bounded-induction-rebase-companions-p8ekt8vt`;
* 6 from `/tmp/ipra-bounded-induction-postmerge-wgkld2w0`.

For example, the selected `PRAPositiveMapPack` object `5902bb1a…` is recorded
with source `87a34587…`; its four recorded project inputs match the overlay.
This is consistent with the repaired packed-normal edge in the earlier trace,
and should not be confused with the old `37518194…` ancestry mismatch. The
selected `IPRANativeTheory` and `PRABoundedFormula` records likewise have
matching selected project inputs. Full digests, paths and edges are in the
receipt, including any discrepancy if the check is adapted to a future state.

This is a **recorded project-edge result**, not a complete provider-closure or
source-current claim. Sixteen additional Foundation, Lean or Mathlib names
appear as nonproject imports of these 172 rows; their objects, companions,
transitive histories and dynamic loads are not validated here. The previous
trace has its own distinct nonproject frontier and other limitations. The
847-module PRA ancestor was an author-side run, with inherited package
ancestry. A successful recorded edge comparison does not establish source
compatibility with the current workspace, authenticate every dependency of a
new 88/30 build, or prove its iPRA endpoint.

From `Computability/DiophantineConsistency` reproduce the pinned observation:

```
python3 -I -S -B research/adaptive87-peer-boundary-producers/check.py | cmp - research/adaptive87-peer-boundary-producers/receipt.json
```

The prior trace's receipt and the prior source-origin inventory are pinned;
this checker does not rerun either audit. It reads but does not mutate retained
`/tmp` evidence, and fails if a required path or hash changes. No Lean, build,
clean, staging, package replay, or new axiom check was performed.
