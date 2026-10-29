# The reverse bounded-collection implication

`ParsonsCollection.collection_reverse` is an actual pure LK derivation of

    (∃B, ∀i<n, ∃y<B, D(i,y)) → (∀i<n, ∃y, D(i,y))

for any two-variable formula D, any term n, and arbitrary other free
parameters. `prove_collection_reverse` embeds that derivation in the explicit
rule calculus over any base theory. The implementation gives a separate
fixed-bound proof and verifies the eigenvariable shifts needed to eliminate
the outer bound. It uses no induction or collection hypothesis.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`. Both objects and complete logs match. Eight
printed axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`.
The [16-file replay manifest](parsons-collection-replay/FILES.json) has SHA-256
`94a98770d020ad12b02ac384460da489cdda9d3c2644df0e4228a70744eba11c`.
Direct prerequisites were previously built `ParsonsPrenex`, `ParsonsRule`,
and `ParsonsGuard`; Foundation/Mathlib objects remain an inherited boundary,
not an independent transitive source audit. Scratch attempts around binder
order, substitution, and eigenvariable shifts failed before being fixed; the
console logs were not retained.

This proves only the easy direction of the concrete collection equivalence.
The converse, general strict Π₂ normalization, the full cut-free recursion,
and PRA witnessing remain open; no collection principle is assumed.

A third independent replay at `/tmp/parsons-collection-build-yph8wx_o`
matched both source and object hashes and full logs of the author builds.
All 16 author-manifest entries matched. The direct prenex provider matches
the independently replayed object. The [independent replay](parsons-collection-independent-replay/)
has the same inherited Foundation/Mathlib boundary.
