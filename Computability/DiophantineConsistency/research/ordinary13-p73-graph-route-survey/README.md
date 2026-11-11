# P73 graph-only route and collision observation

This is a **read-only, point-in-time survey**, not a Lean build, a `lean
--deps` result, a compatibility proof, or build-readiness approval. It refines
the independently reviewed [P73 provider survey](../ordinary13-p73-provider-preflight/README.md)
for the graph-only stage of the uncompiled [91-operation draft](../ordinary13-p73-share91-lean-draft/README.md).
It creates no build tree and starts no Lean process.

The intended source order is `Compact44.FreeJ13`, `Compact44.P73Graph`, then
the new `P73Shared91` client. Line-parsed source imports say `FreeJ13` uses
the retained P72 `FreeJSumSquares` and `FreeJSignedTransport` plus
`Mathlib.Tactic.LinearCombination`; `P73Graph` uses the newly produced
`FreeJ13` and that Mathlib object; the client imports the newly produced
`P73Graph`. These are proposed direct routes and must still be confirmed by
the future guarded `lean --deps` calls.

For analysis only, the survey considers a future isolated output root first
(it is **not created or inspected**), followed by the existing P72 `lib`,
guarded package overlay, and toolchain library. It does not set `LEAN_PATH` or
infer the effective search path of any Lean process. A future runner must
independently check and sanitize its environment and verify actual lookup order.
It must not add a separate base or failed-run root by default: the P72 tree
already links the base, and [the prior survey](../ordinary13-p73-provider-preflight/README.md)
records different `ModelDifferenceRing` object hashes for the same source in
the P72 and two FAILED-parent roots.

At the frozen observation, the two P72 frontier objects' recorded ancestry
contains 13 P72 producers and 17 base producers. The survey checks their 86
recorded direct edges, 1,050 P72 direct-guard slots and 170 base output slots,
plus producer and declared-source routes, and inventories all 54 resulting
module names, including the three future output names. Across
the three named existing roots it found no selected-route disagreement and no
different-hash companion candidates for these names. `Init.olean` appeared in
both package and toolchain roots as the same real file. The three future
output names had no observed artifacts in those roots, the separate base or
the project build root; their source snapshots were absent from P72's source
snapshot tree. This is a filesystem observation, not a guarantee that a later
isolated output root or an unobserved search path is empty.

For a broader shadowing check, all 1,681 `.olean` names in the retained P72
overlay matched the 681 extension producers plus 1,000 base names; no broken
`.olean` was observed. Comparing those names across P72 against the package and
toolchain roots found no cross-root intersections for the 13 inspected object,
private/server, IR, interface, hash and shared-library suffixes. This broad
name check does not authenticate all 1,681 objects or prove that no other
suffix or dynamic loader is relevant. The preceding retained-route survey is
rerun to recheck its recorded hashes and companion guards before these
observations are made.

## Reproduce

From the repository root:

```
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary13-p73-graph-route-survey/inspect.py
```

It emits JSON to stdout and requires the retained `/tmp` providers. The frozen
[observation](observation.json) is one run; HEAD and resource samples can
change. The inspector pins and reruns the earlier read-only provenance survey,
traces the two graph frontier objects through captured stage records, observes
the specified roots and suffixes, and records route issues and different-hash
candidates. It uses bounded subprocesses and does not create an output tree.

The frozen `/tmp` free-space sample is about 5.05 GB, below the established
5,100,000,000-byte sampled stop; it is not reserved. Line parsing, historical
direct-edge captures, package-transitive imports, dynamic loading, transient
changes, and Lean's actual path resolution remain outside this observation.
Any future runner must use a fresh output directory, independently reviewed
object/source and companion guards, actual direct-route checks, the established
4-GiB sampled child RSS, 10-GiB host floor, 5.1-GB sampled disk stop and
per-stage time limits, plus independent prelaunch review and slot allocation.
No prior artifacts are deleted. Neither this survey nor the uncompiled draft
proves a new Lean theorem or binds Lean to the JSON or rendered PDF.
