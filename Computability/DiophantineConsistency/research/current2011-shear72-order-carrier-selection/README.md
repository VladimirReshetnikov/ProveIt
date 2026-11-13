# Isolated lighter import alternative for the forward order lemma

The original `ShearOrder.lean.src` imports `ModelCarrierSpheres`, but its only nonstandard project name is `Carrier65.core` (including the `c`, `f`, `rank`, `V` projections). The checked source definition of `Carrier65.core` contains exactly the displayed signed V expression and coordinate-6 T. The remaining non-tactic names are `CommRing`, `LinearOrder`, `IsStrictOrderedRing`, `mul_nonneg`, `sub_nonneg`, and `le_of_not_gt`; the checker locates their declarations or uses in pinned Mathlib algebra/order sources. These textual observations do not establish their availability from the new imports. Its tactics include `linarith`, `nlinarith` and `by_contra`.

The separate inert alternative here replaces the one original import with three explicit source imports: `DiophantineConsistency.Carrier65`, `Mathlib.Tactic.Linarith` and `Mathlib.Tactic.ByContra`. Every byte following the original import line is unchanged. The selected Mathlib `Linarith` source imports its frontend, which declares `nlinarith`; the ByContra source is included explicitly as a precaution. These are source/interface observations, **not** a verified import closure or Lean elaboration. Whether all algebra/order instances, tactic syntax, `open Carrier65`, `nlinarith only` and the defining `change` elaborate must be checked in a coherent environment.

The isolated `selection.json` changes only the `ShearOrder` draft source/import entry and its direct frontier: `ModelCarrierSpheres` is dropped and `Carrier65` plus two unexamined Mathlib tactic modules are added. This does not show `ModelCarrierSpheres` is absent transitively, prove project or package object compatibility, select providers, or change the original source and previous selections. In particular the previously observed `ModelDifferenceRing` object disagreement remains an unclosed provider boundary. The direct project source and external package source headers are pinned for inspection; no claim that the observed source produced a chosen object is made.

The checker verifies the exact import-only source delta, the sole selected-entry/frontier changes, explicit core definitions and tactic entry points, all selected direct-draft edges and topological order. It does not parse Lean, build, run `#print axioms`, authenticate providers, prove the order lemmas, or establish the 72/46 iPRA endpoint.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/current2011-shear72-order-carrier-selection/check.py | cmp - research/current2011-shear72-order-carrier-selection/receipt.json
```

No Lean/build/staging or historical-source edits were performed.
