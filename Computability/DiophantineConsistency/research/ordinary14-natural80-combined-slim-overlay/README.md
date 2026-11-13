# Inert natural-80 endpoint overlay with slim imports and source alternatives

This **unelaborated source-only** overlay extends the independently reviewed
[natural-81 combined overlay](../ordinary14-natural81-combined-slim-overlay/README.md)
to the unelaborated natural-80 endpoint's pinned
[lexical inventory](../ordinary14-natural80-endpoint-import-inventory/README.md).
It contains 184 inert `.lean.src` snapshots. No Lean source tree has been
materialized, and no Lean parsing, elaboration, dependency-resolution or axiom
check has run. The original sources, earlier snapshots and their receipts are
not modified.

An [independent source review](../../reviews/ordinary14-natural80-combined-slim-overlay-independent/README.md)
checks the snapshot composition, selected fixes and lexical imports without
running Lean or establishing provider closure.

All 173 natural-81 modules are included: 171 snapshots are byte-identical to
the earlier combined overlay, while `PartialShift82To74` and
`GraphPredecessors82` use the separately reviewed
[`partial`-identifier alternatives](../ordinary14-natural-partial-keyword-patch/README.md).
Those two snapshots replace 8 and 7 code-token uses of the helper name with
`partialValuation` while preserving the documented comment and module imports.
This addresses a source-level parser hazard suggested by the inspected Lean
parser sources; no Lean parser has confirmed it is a failure or that these
alternatives resolve it. The earlier predecessor-witness commutation alternatives
and six root74 slim-import refactors remain present in the 171 unchanged
snapshots. None of these alternatives has been elaborated.

The other 11 snapshots are byte-identical to the additional original draft
modules in the natural-80 endpoint inventory: `P80NaturalForcedGamma`,
`Natural80Partial74`, `Natural80JPos`, `Natural80OwnZeroNorm`,
`Natural80GuardGap`, `Natural80MainPairs`, `GammaZeroNarrow`, `GammaPremises`,
`Natural80GammaClient`, `Natural80GammaShift` and `Natural80Endpoint`. The
separate compact model-port draft is not imported by this endpoint and is not
in the 184-module closure.

The read-only checker pins the natural-81 combined and natural-80 endpoint
inventories; rechecks all 184 original source hashes; verifies every reused
snapshot against its previous overlay hash; verifies the exact 15 keyword-token
edits against the two pinned alternatives; and checks all 11 additions against
their original drafts. It follows the resulting snapshots' simple initial
import headers to `Natural80Endpoint`, checks every bare import is present,
all 184 modules are reachable and the order is acyclic, and compares all 40
directly named qualified project-source hashes with the pinned natural-80
inventory. The sole qualified name removed from the original natural-80
headers is `C44Short15Facts`, due to the earlier slim refactor. The checker
writes a deterministic JSON receipt to stdout; it never runs Lean.

The combined headers directly name three qualified project modules beyond the
natural-81 combined overlay's direct set:

* `DiophantineConsistency.ArithmeticAdaptiveTransport2011`
* `DiophantineConsistency.BFS943.Direct80IndexOne`
* `DiophantineConsistency.Compact44.DirectMainNorm`

These are **lexical source differences**, not a resolved provider cut or a
claim that any corresponding compiled object is missing or compatible. This
checker does not traverse qualified sources' transitive imports, authenticate
Foundation/Mathlib/toolchain or runtime providers and their companions, resolve
Lean search paths, exclude external object collisions, reserve resources, or
establish provider ancestry. Its header parser is bounded to these pinned
simple draft headers; it is not Lean's resolver.

A future isolated build needs a separately reviewed source materialization and
full provider/companion and resource plan, guarded Lean dependency and compile
runs, executed axiom reports, and independent postflight. This overlay does not
establish a model bridge, a proof in iPRA, an axiom closure, or a binding to
physical coefficients or the displayed PDF.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary14-natural80-combined-slim-overlay/check_source.py | cmp - research/ordinary14-natural80-combined-slim-overlay/inventory.json
```
