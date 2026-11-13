# Inert natural-79 endpoint overlay with reviewed source alternatives

This **unelaborated source-only** overlay extends the independently reviewed
[natural-80 combined overlay](../ordinary14-natural80-combined-slim-overlay/README.md)
to the initial-header closure of the proposed
[natural-79 endpoint](../ordinary14-natural-forced-w79-ipra-draft/README.md).
It contains 195 inert `.lean.src` snapshots. No Lean source tree has been
materialized, and no Lean parsing, elaboration, dependency resolution or
axiom check has run. Original sources, older overlay snapshots and their
receipts are unchanged.

An [independent source review](../../reviews/ordinary14-natural79-combined-slim-overlay-independent/README.md)
checks the snapshot composition and lexical closure without running Lean or
establishing provider or axiom closure.

All 184 natural-80 overlay snapshots are included **byte-for-byte**. This
retains the prior root74 slim import/reference refactors, two inert
predecessor-witness order alternatives, and the two inert `partialValuation`
keyword alternatives selected by that overlay. The other 11 modules are pinned
byte-for-byte copies of current natural-79 endpoint drafts:

* `P79NaturalForcedW`, `Natural79ResidueShapes`, `Natural79ZeroWUnits` and
  `Natural79ConcreteUnits`;
* `Natural79ZeroWJPos`, `Natural79ZeroWMainNorm`, `ForcedWDivisibility` and
  `Natural79ZeroWRootCut`;
* `Natural79ZeroWDivisibility`, `Natural79WShift` and `Natural79Endpoint`.

The read-only checker pins the natural-80 overlay inventory and each added
source, rechecks all 195 original source bytes and every reused snapshot,
checks the added sources are copied unchanged, and follows the resulting
snapshots' actual simple initial import headers backward from
`Natural79Endpoint`. It verifies all bare imports are present, all 195
snapshots are reachable, and their lexical order is acyclic. It also rejects
bare-source name duplicates **within the research tree only**, non-inert or
symlink entries in this overlay, and drift in the 42 directly named qualified
project sources or the two directly named Mathlib source files. Its JSON
receipt records per-source hashes and the lexical order. The checker does not
run Lean or materialize compiled modules.

The two directly named project sources added relative to the natural-80
overlay are:

* `DiophantineConsistency.BFS943.Direct80NaturalProjection`;
* `DiophantineConsistency.Compact44.ReducedNormSigned`.

The `ForcedWDivisibility` draft also directly imports
`Mathlib.Algebra.Ring.Basic` and `Mathlib.Tactic.Ring`. These four names are
**lexical source additions**, not a resolved provider cut or a claim about
missing or compatible compiled objects. Their presence introduces further
provider, transitive-import and companion obligations. Existing natural-80
provider observations do not automatically authenticate these new routes.
The two Mathlib source hashes in the receipt do not prove their compiled object
provenance.

The header parser handles the simple initial imports in these checked draft
sources and is not Lean's resolver. It does not inspect qualified-source
transitive imports, Foundation/Mathlib/toolchain or runtime dependencies and
companions, competing sources or objects outside the research-tree name scan,
search precedence, external output collisions, resource availability or
provider provenance. A future build needs a separately reviewed isolated source
materialization, provider and companion plan, guarded Lean dependency/compile
runs, executed axiom reports and independent postflight.

The overlay does not establish the 79 graph/model or iPRA endpoint, the
positive-w proof, any axiom closure, or physical coefficient/PDF binding.
The two earlier source hazards and their selected inert fixes remain untested
by Lean. The 79 endpoint's symbolic compact tuple is distinct from the
coefficients and graph displayed in the Carrier65 PDF.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary14-natural79-combined-slim-overlay/check_source.py | cmp - research/ordinary14-natural79-combined-slim-overlay/inventory.json
```
