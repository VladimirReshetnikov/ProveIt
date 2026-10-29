# From an IΣ₁ proof to a normalized cut-free sequent

`ParsonsTheoryNormalize.normalizeTheory` takes an actual Foundation proof
from any base theory augmented by an induction scheme. It partitions the
finite list of used axioms into base axioms and induction formulas satisfying
the specified scheme predicate. It retains certificates for both lists,
reorders the original finite sequent, applies `ParsonsClosure` to replace
the negative closed induction axioms by parameter-closed counterexample
matrices, and returns a cut-free proof of the resulting sequent.
`normalizeISigma` specializes this construction to Foundation's actual IΣ₁
and PA-minus; `isigma_has_normalized` provides its proof-existence form.
Classical choice selects a partition and representative formulas, and no
claim is made that this proof transformer is primitive recursive.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`. Both objects and complete logs match; four
printed axiom reports use only `propext`, `Classical.choice`, and
`Quot.sound`. The [16-file replay manifest](parsons-theory-normalize-replay/FILES.json)
has SHA-256 `cf041b80f3e7fbfb4ea4dcbaf4635aa5ae7f4ca1748b52c8a3e905d455fcbc48`.
Direct prerequisites were previously built `ParsonsClosure`,
`ParsonsInductionCase`, `ParsonsRule`, `ParsonsGuard`, and
`ParsonsSelection`; Foundation/Mathlib objects remain an inherited boundary
and were not independently re-audited. Exploratory scratch failures around
partition proof branches and sequent membership were fixed; their logs were
not retained.

This result starts with an actual IΣ₁ proof and completes the preprocessing
and cut-elimination stage. It does not translate the normalized cut-free proof
into the induction-rule calculus or give a PRA proof. The existential-block
cases, strict Π₂ side-form adapter, and the witnessing theorem remain open.

A third independent replay at `/tmp/parsons-theory-normalize-build-1bz01iwb`
matched both source and object hashes and full logs of the author builds.
All 16 author-manifest entries matched. The direct closure provider matches
the independently replayed closure object, and the other direct providers
match the previously reviewed induction-case overlay. The
[independent replay](parsons-theory-normalize-independent-replay/) has the
same inherited Foundation/Mathlib boundary.
