# Strict Π₂ disjunction normalizer

For two strict formulas `∀x ∃y A(x,y)` and `∀u ∃v B(u,v)`, Lean constructs
actual PA-minus rule proofs in both directions between their disjunction and
`∀x ∀u ∃y ∃v (A(x,y) ∨ B(u,v))`, retaining arbitrary free parameters. If both
matrices are bounded, the combined matrix is bounded. This is one strict
prenex normalization component, not a normalization theorem for arbitrary
Foundation Π₂ formulas or the completed guard adapter. The proof uses
classical metatheoretic completeness and is noncomputable.

Two isolated builds against the reviewed Parsons provider matched sources,
objects and complete logs. The driver checks direct and inherited local
provider hashes. The [independent driver and logs](parsons-prenex-pi2-or-root-replay/)
and [author packet](parsons-prenex-pi2-or-author-replay/) are retained.
Foundation, Mathlib and completeness objects remain inherited boundaries.
