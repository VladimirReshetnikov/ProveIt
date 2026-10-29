# Two explicit existential witnesses

`ParsonsPrenexPair` constructs rule-calculus proofs in both directions between
`(∃y R(y)) ∨ (∃x Q(x))` and `∃x ∃y (R(y) ∨ Q(x))`. The two bound variables
remain separate: no pairing function or witness encoding is assumed. The
matrix construction and its eigenvariable identities retain arbitrary free
parameters. `pair_strict_matrix` certifies the matrix is bounded if Q and R
are bounded. This therefore handles disjunction of two strict Σ₁ formulas
and yields a strict Σ₁ form with an explicit two-variable existential block.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`. Both objects and complete logs match. Seven
axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`. The
[16-file replay manifest](parsons-prenex-pair-replay/FILES.json) has SHA-256
`e7a4daf1c40cb1ee0c93cd1dc9760cb7d97b14b298a16a6a10a77066c216afc7`.
Direct prerequisites were previously built `ParsonsPrenex`, `ParsonsRule`, and
`ParsonsGuard`; Foundation/Mathlib objects are an inherited boundary, not a
fresh transitive source audit. Scratch attempts around bound/free variable
rewritings failed before being fixed; their console logs were not retained.

This is a real two-witness fragment, not an arbitrary-length or general Π₂
normalization algorithm. Bounded collection, remaining cut-free recursion,
and PRA witnessing remain open.

A third independent replay at `/tmp/parsons-prenex-pair-build-1s6r2ec7`
matched both source and object hashes and full logs of the author builds.
All 16 author-manifest entries matched. The direct prenex provider matches
the independently replayed object. The [independent replay](parsons-prenex-pair-independent-replay/)
has the same inherited Foundation/Mathlib boundary.
