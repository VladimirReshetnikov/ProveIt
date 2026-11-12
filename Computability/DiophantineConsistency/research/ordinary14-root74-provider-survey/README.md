# Read-only root74 source and provider survey

This is a **bounded point-in-time audit**, not a Lean build plan or readiness
certificate. It compares the pinned root74 and slim-root78 source inventories,
retained P72/base metadata, selected source/object/companion hashes, Init and
candidate output names. It never runs Lean or modifies retained evidence.

The root74 slim overlay has 159 bare snapshots: 138 also appear byte-identical
in the reviewed slim root78 overlay, 21 names are new, and `Root78Endpoint` is
omitted. Among the original root74 inventory's 31 directly qualified project
imports, the retained P72/base path lacks `C44Short15Facts`, `FreeJ13`,
`FreeJ13Halt`, and `DiscreteOrderedRingFacts` objects. A simple initial-header
walk of the slim overlay's 30 direct imports, stopping at the first P72/base
object, yields only the last three names as additional source candidates, 31
observed frontier names and four external Mathlib object names. This is lexical
source/presence evidence, not `lean --deps`, a proven minimal stage list or a
global object search.

The P72 PASS row for `ArithmeticAdaptiveFactorUnits2011` matches its current
source/object, three captured direct objects and recorded direct-guard slots;
a subsequent P72 row's recorded guard slots also match. The retained base PASS
record for `ArithmeticNegativeNorms` matches its source/object, three direct
inputs and ten recorded output slots. Object presence and recorded companion
absence do not prove package-transitive or runtime compatibility. The selected
`DiscreteOrderedRingFacts` source has neither a P72 source-snapshot entry nor
a base producer record or object at those two roots; other roots are unsearched.
The four external Mathlib object hashes and resolved paths are included, without
asserting their transitive provenance.

The guarded package and selected toolchain Init `.olean`, `.olean.private`,
`.olean.server` and `.ir` resolve to the same files. Package `Init.ilean` is
absent while the core counterpart exists; actual Lean search resolution remains
unobserved. A bounded same-name scan covers the 159 bare draft names and the
three candidate qualified names, 13 historical output/companion suffixes and
five selected roots; a missing hit does not prove complete collision freedom.
The failed P72 retry roots must not be mixed with the selected provider route.

Run, from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary14-root74-provider-survey/inspect.py | cmp - research/ordinary14-root74-provider-survey/observation.json
```

This expects the retained `/tmp` evidence to remain intact. Current free disk
was below the strict 5,100,000,000-byte Lean-run floor at sampling and is not
reserved. Exclusive slot allocation, a complete immutable transitive
provider/companion audit, actual guarded Lean dependency resolution, all
source elaboration, axiom replay, iPRA endpoint, and physical byte/PDF binding
remain open.

Independent source review: [root74 provider survey](../../reviews/ordinary14-root74-provider-survey-independent/README.md).
