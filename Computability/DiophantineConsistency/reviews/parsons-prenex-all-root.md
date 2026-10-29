# Moving a universal quantifier through disjunction

`ParsonsPrenexAll` supplies explicit LK derivations in both directions between
`E ∨ ∀x Q(x)` and `∀x (Q(x) ∨ E)`, preserving all free parameters of E by an
explicit bound-variable shift. It turns both directions into rule-calculus
proof transformers over the same arbitrary base theory, and gives a
proof-existence equivalence. This is the universal-quantifier counterpart to
`ParsonsPrenex` and is usable when moving the outer universal quantifiers of
strict Π₂ side formulas.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`. Both objects and complete logs match. Six
axiom reports contain no axioms beyond `propext`, `Classical.choice`, and
`Quot.sound`; the pure LK derivations do not depend on choice. The
[16-file replay manifest](parsons-prenex-all-replay/FILES.json) has SHA-256
`c9634ada60cdf325b0b463a47185d78292fa1d028b79582dbaceaf32d4c621fb`.
Direct prerequisites were previously built `ParsonsCollection`,
`ParsonsPrenex`, `ParsonsRule`, and `ParsonsGuard`; Foundation/Mathlib objects
remain an inherited boundary, not a fresh transitive source audit.

This proves a quantifier/disjunction transformation, not the complete strict
Π₂ adapter. Bounded collection, the global cut-free translation, and PRA
witnessing remain open.

A third independent replay at `/tmp/parsons-prenex-all-build-c11ln7y1`
matched both source and object hashes and full logs of the author builds.
All 16 author-manifest entries matched, and the direct collection provider
matched its independently replayed object. The [independent replay](parsons-prenex-all-independent-replay/)
has the same inherited Foundation/Mathlib boundary.
