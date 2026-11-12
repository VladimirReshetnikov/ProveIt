# Independent review: natural-79 combined slim source overlay

The [natural-79 overlay](../../research/ordinary14-natural79-combined-slim-overlay/README.md)
accurately describes its bounded source composition. Both the original receipt
and the independent checker below reproduce. This is a byte and simple-header
review, not Lean parsing, elaboration, provider resolution or an iPRA theorem.

The independent checker pins the natural-79 and natural-80 inventories and the
natural-79 checker. It hashes all 195 original source paths and all 195 inert
snapshots, confirming that 184 snapshots are byte-identical to the earlier
natural-80 overlay and the remaining 11 are byte-identical to the listed
natural-79 source drafts. It verifies the snapshot directory contains exactly
those regular non-symlink `.lean.src` files, and finds one original `.lean`
candidate for each module **within the research tree**. This inherited-byte
comparison retains the natural-80 overlay's previously reviewed slim-import,
predecessor-order and `partialValuation` alternatives; it does not re-elaborate
them or establish that they are correct Lean proofs.

The checker reparses the simple initial import lines, verifies every bare
import precedes its consumer in the recorded order, and independently
traverses the imports backwards from `Natural79Endpoint` to reach all 195
snapshots. It checks the paths and hashes of all 42 directly named project
sources and both directly named Mathlib sources. Relative to the prior
natural-80 overlay the two additional direct project names are
`BFS943.Direct80NaturalProjection` and `Compact44.ReducedNormSigned`;
the Mathlib names are `Mathlib.Algebra.Ring.Basic` and `Mathlib.Tactic.Ring`.
These are source-header comparisons, not Lean's resolved provider set.

The check shares the pinned earlier inventory and does not authenticate
historical compiled objects, prove source-to-object provenance, follow
qualified or external transitive imports, inspect runtime and companion files,
exclude competing source or object providers outside the research-tree name
scan, reserve resources, or execute Lean and axiom reports. In particular,
matching these source bytes to an inert overlay does not prove the 79 graph's
model equivalence, the internal iPRA endpoint, or a physical coefficient/PDF
binding.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-natural79-combined-slim-overlay-independent/check.py | cmp - reviews/ordinary14-natural79-combined-slim-overlay-independent/result.json
```
