# A proved strict Σ₁ prenex step

`ParsonsPrenex` supplies explicit LK derivations in both directions between
`E ∨ ∃x Q(x)` and `∃x (Q(x) ∨ E)`. The bound-variable shift in the latter
formula preserves all free parameters of E. `prove_disjunction_to_exs` and
`prove_exs_to_disjunction` turn these into proof transformers over the same
arbitrary `ParsonsRule` base theory; `provability_equiv` gives the corresponding
proof-existence equivalence. When E and Q are bounded, `strict_matrix`
certifies that the new existential has a bounded matrix, so this is a real
strict Σ₁ normalization fragment. The construction uses ordinary first-order
logic and a zero term for the case where E already holds.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`. Both objects and complete logs match. The
seven axiom reports contain no axioms beyond `propext`, `Classical.choice`,
and `Quot.sound`; the three pure LK derivations do not depend on choice.
The [16-file replay manifest](parsons-prenex-replay/FILES.json) has SHA-256
`992977a8a27fc0f4c8e55fd2b915dab228089c312854bdf78b76d6a82b5fb8ff`.
Direct prerequisites were previously built `ParsonsRule` and `ParsonsGuard`;
Foundation/Mathlib objects are an inherited boundary, not a fresh transitive
source audit. Scratch attempts around the guard's eigenvariable shift and
sequent order failed before being fixed; their console logs were not retained.

This proves one connective/quantifier transformation. It is not a complete
strict Σ₁ or Π₂ adapter, does not prove the bounded collection implication,
and does not establish the global cut-free translation or PRA witnessing.

A third independent replay at `/tmp/parsons-prenex-build-zxpaye1c` matched
both source and object hashes and full logs of the author builds. All 16
author-manifest entries matched. The direct rule and guard providers match
the previously reviewed overlay. The [independent replay](parsons-prenex-independent-replay/)
has the same inherited Foundation/Mathlib boundary.
