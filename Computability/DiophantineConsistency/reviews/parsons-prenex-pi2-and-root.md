# Strict Π₂ conjunction normalizer

For two strict formulas `∀x ∃y A(x,y)` and `∀u ∃v B(u,v)`, Lean constructs
actual PA-minus rule proofs in both directions between their conjunction and
`∀x ∀u ∃y ∃v (A(x,y) ∧ B(u,v))`, retaining arbitrary free parameters. If both
matrices are bounded, the combined matrix is bounded. This is one strict
prenex normalization component, not a normalization theorem for arbitrary
Foundation Π₂ formulas or the completed guard adapter. The proof uses
classical metatheoretic completeness and is noncomputable.

Two isolated builds against the independently replayed disjunction provider
`/tmp/parsons-prenex-pi2-or-independent-_zzb0w81/lib` matched source, object
and complete-log hashes. The driver checks the frozen local providers. The
[independent driver and logs](parsons-prenex-pi2-and-root-replay/) and
[author packet](parsons-prenex-pi2-and-author-replay/) are retained.
Foundation, Mathlib and completeness objects remain inherited boundaries.
