# Inert natural-81 endpoint overlay with slim imports and predecessor edits

This **source-only, unelaborated** overlay combines the earlier
[root74 slim snapshots](../ordinary14-root74-slim-overlay/README.md) with
all additional drafts in the pinned [natural-81 endpoint lexical inventory](../ordinary14-natural81-endpoint-import-inventory/README.md).
All 173 module snapshots use the inert `.lean.src` suffix. No Lean source
root has been materialized, and no Lean, dependency-resolution or axiom
check has run. The original drafts, earlier overlays and their receipts are
not edited.

An [independent source review](../../reviews/ordinary14-natural81-combined-slim-overlay-independent/README.md)
checks the snapshots, edits and lexical closure. It also flags that this
overlay retains the likely reserved helper name discussed in the separate
[keyword alternatives](../ordinary14-natural-partial-keyword-patch/README.md);
those alternatives are not selected here.

Of the 173 snapshots, 158 are byte-for-byte the corresponding root74 slim
overlay snapshots. Those snapshots contain the six independently reviewed
slim refactors (four import and six reference replacements). The remaining
15 modules are the natural-81 inventory additions, including its endpoint;
`Root74Endpoint` from the older overlay is omitted. Thirteen additions are
copied byte-for-byte from their pinned original source drafts. The other two
use the independently source-reviewed [predecessor-order alternatives](../ordinary14-natural-predecessor-order-patch/README.md):
`Natural81JShift` explicitly commutes the successor witness in `simpa`, and
`Predecessors82` explicitly commutes each of three witnesses. These changes
address a source-level mismatch/risk based on the inspected library signature;
no Lean run has confirmed either a failure or a fix.

The read-only checker pins both earlier inventory byte hashes and the two
original/alternative source hashes; rechecks all 173 original source hashes;
verifies each shared snapshot against the exact old-to-slim import/reference
substitutions; verifies the two precise witness edits; checks all other
additions are unchanged; and follows the snapshots' actual simple initial
import headers to `Natural81Endpoint`. It checks bare-name completeness,
acyclic order, all 173 modules' lexical reachability, and the hashes of the
37 directly named qualified project source files against the natural-81
inventory. The checker writes only a deterministic JSON receipt to stdout;
it neither changes files nor calls Lean.

The combined headers directly name seven qualified project modules beyond the
root74 slim overlay's direct set:

* `DiophantineConsistency.Compact44.CompactKernelSplit`
* `DiophantineConsistency.Compact44.CompactSymbolicModelIff`
* `DiophantineConsistency.Compact44.IPRAOrdinary12`
* `DiophantineConsistency.HAExpressionNoZeroEquiv`
* `DiophantineConsistency.IPRAExpressionNative`
* `DiophantineConsistency.IPRAReferenceInductionConversion`
* `DiophantineConsistency.IPRAStandardTheory`

These names are a **lexical source difference**, not a list of missing or
compatible `.olean` providers. In particular, the previously sampled root74
provider boundary and ordered plan do not automatically cover these sources
or the 15 added drafts. This checker does not traverse qualified sources'
transitive imports, account for Foundation/Mathlib/toolchain or runtime
providers and companions, select a search path, detect external object
collisions, reserve resources or establish provider provenance. Its simple
header parsing is validated against the pinned draft inventories for these
sources only; it is not Lean's resolver.

A future isolated build would need a separately reviewed materialization,
full dependency/provider and companion plan, resource guards and axiom
reports, followed by Lean elaboration and independent postflight. This packet
does not establish a graph/model bridge, a derivation in iPRA, an axiom
closure, or a connection to physical coefficient bytes or the PDF.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary14-natural81-combined-slim-overlay/check_source.py | cmp - research/ordinary14-natural81-combined-slim-overlay/inventory.json
```
