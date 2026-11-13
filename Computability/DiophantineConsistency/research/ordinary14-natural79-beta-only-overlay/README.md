# Inert natural-79 beta-only endpoint overlay

This source-only overlay selects the four independently reviewed
[beta-only alternatives](../ordinary14-natural79-beta-only-zero-w-draft/README.md)
on top of the [corrected 196-module reflection overlay](../ordinary14-natural79-corrected-reflection-overlay/README.md).
It contains **195** distinct inert `.lean.src` snapshots: 191 unchanged previous
snapshots and four selected beta-only alternatives. Previous snapshots, source
files and receipts remain unchanged; no Lean sources or objects are materialized.

An [independent source review](../../reviews/ordinary14-natural79-beta-only-overlay-independent/README.md)
checks the 195 selected snapshots and lexical closure without running Lean.

The read-only checker pins the previous inventory and every previous selected
and original source, the beta-only author and independent-review receipts, the
four exact alternative snapshots, and all directly named project and external
sources. It follows the actual simple initial headers from `Natural79Endpoint`,
checks unique names, all reachable bare imports, absence of bare-import cycles,
and records each source hash, selected source, imports and a dependency-first
order. Its parser is limited to these headers; it is not Lean's resolver.

The sole previous module no longer reachable is `Natural79ZeroWJPos`: both
imports that made it reachable were removed in the reviewed alternatives. Its
pair-unit evaluator was copied into `Natural79ZeroWMainNorm`, with attribution,
so this is a header/source selection observation, not a claim that its
mathematics or providers became unnecessary. All four alternative modules are
reachable. The 80 endpoint and `StrictK0Symbolic` remain selected because the
endpoint still imports them; their prior obligations remain.

The set of directly named qualified project sources remains **41**, and the
set of directly named external sources remains the same **three** Foundation
and Mathlib modules. The corrected reflection helper and its explicit
Foundation import are retained. The prior corrected reflection
[provider projection](../ordinary14-natural79-corrected-reflection-provider-cut/README.md)
was an observation of a qualified-source frontier for the same direct names;
this overlay receipt does not rescan or authenticate its objects, resolve
transitive imports, or establish a current collision boundary. The previous
201-stage ordered plan includes the omitted module and prior four snapshots and
therefore is **not** a plan for this selected overlay.

**This overlay is not build-ready.** No Lean parsing, elaboration, proof or
axiom report has run. The beta-only model argument, graph bindings, provider and
companion provenance, complete dependency closure, search order, runtime,
resource and collision conditions still require independent verification. It
does not establish the iPRA equivalence or the separate physical Carrier65
coefficient/PDF binding.

From the repository root, while the pinned Foundation source and retained
workspace package sources remain present:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary14-natural79-beta-only-overlay/check_source.py | cmp - Computability/DiophantineConsistency/research/ordinary14-natural79-beta-only-overlay/inventory.json
```
