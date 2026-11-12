# Natural-79 endpoint: inert corrected-reflection overlay

This unelaborated source snapshot contains **196** distinct inert `.lean.src`
modules. It extends the reviewed [195-module natural-79 overlay](../ordinary14-natural79-combined-slim-overlay/README.md)
with the [corrected slim reflection helper](../ordinary14-natural79-slim-reflection-import-repair/README.md)
and the [slim divisibility client alternative](../ordinary14-natural79-dvd-reflection-slim-draft/README.md).
There are no changes to older snapshots, original sources or receipts.

An [independent source review](../../reviews/ordinary14-natural79-corrected-reflection-overlay-independent/README.md)
checks the selected changes, retained snapshots and lexical order without
running Lean or establishing provider closure.

The selection consists of 194 byte-for-byte copies of the prior overlay, one
client alternative with exactly its import and qualified theorem reference
changed, and the added helper. The helper is the prior generic reflection copy
with exactly one additional Foundation import. Thus the root74 slim
alternatives, predecessor witness-order alternatives and `partialValuation`
keyword alternatives already selected by the prior overlay are retained.

The read-only checker pins the prior inventory, every prior overlay and
original source, the helper and client alternatives, all directly named project
and external sources, and the previous corrected [lexical provider projection](../ordinary14-natural79-corrected-reflection-provider-cut/README.md).
It verifies that there are exactly 196 unique selected module filenames,
that each is a regular inert snapshot, and that each selected source has the
expected bytes. It follows the snapshots' actual simple initial import headers
from `Natural79Endpoint`, checks all bare imports resolve within this set,
rejects cycles and unreachable snapshots, and records every module hash, its
bare and qualified direct imports, and a dependency-first topological order.
The header parser is deliberately limited to these simple source headers; it is
not Lean's dependency resolver. Uniqueness here concerns only this selected set,
not every candidate elsewhere in the workspace.

The exact selected headers directly name **41** qualified project sources and
three external modules: Foundation `IOpen.Basic`, Mathlib `Algebra.Ring.Basic`,
and Mathlib `Tactic.Ring`. The original BFS direct projection is no longer a
direct import. The Foundation source observation uses the retained guarded
`/tmp` workspace, not the checkout's empty Foundation directory. The existing
bounded provider projection reports five project-source candidates missing from
the selected P72 frontier and observes the Foundation package object; it is a
point-in-time lexical observation and must be rechecked before use.

**This overlay is not build-ready.** It does not materialize Lean modules or
establish provider and companion provenance, complete transitive dependencies,
search precedence, output collision safety, resource availability, successful
Lean parsing/elaboration or axiom closure. No `#print axioms` was executed.
It does not establish the model argument, the iPRA equivalence, or the physical
coefficient and PDF binding for the separately displayed Carrier65 equation.
Future materialization and compilation require their own reviewed dependency,
provider, resource, collision and postflight checks.

From the repository root, while the pinned guarded Foundation source exists:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary14-natural79-corrected-reflection-overlay/check_source.py | cmp - Computability/DiophantineConsistency/research/ordinary14-natural79-corrected-reflection-overlay/inventory.json
```
