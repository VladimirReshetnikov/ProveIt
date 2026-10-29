# Positive-guarded bounded collection

`ParsonsGuardedCollection.guarded_bounded` constructs an actual PA-minus
rule-calculus proof of

    E ∨ ∃B ∀i<n ∃y<B D(i,y)

from an actual rule-calculus proof of

    E ∨ ∀i<n ∃y D(i,y).

D and E must be Σ₁ in Foundation's hierarchy; n and all free parameters
are arbitrary. The proof forms the guarded total predicate
`(i<n → D(i,y)) ∨ E`, proves it Σ₁, applies the previously established Σ₁
collection rule, and proves the surrounding transformations via semantic
validity, completeness, and specialization of universal closures. The more
general `guarded_collect` accepts any bounded outer predicate K instead of
`i<n`. No collection axiom or finite-extension proof is assumed.

This is a positive-disjunction **proof transformer**, not a derivation of
the formula `(E ∨ H) → (E ∨ C)` or of `H → C` in arbitrary contexts. It is
noncomputable because the actual PA-minus proofs are obtained using
Foundation's model-theoretic completeness and classical choice. It proves
existence of rule proofs, not a primitive-recursive proof transformation or a
proof formalized inside PRA.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`. Both objects and complete logs match. Eight
axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`. The
[16-file replay manifest](parsons-guarded-collection-replay/FILES.json) has
SHA-256 `6146d2c128fe673784ea401500f81f9d42c8ff0f85d7975483906a94d5b3dc85`.
Scratch attempts around term shifts and finite-index semantics failed before
being fixed; their console logs were not retained.

The direct `ParsonsSpecialize` provider has source SHA-256
`db9cde51d8b0bc611d68f2732c3d8b52b005b18883ab038fba400ce7d08c8a6e` and object
SHA-256 `e3009760f0a63f72270970c739cec363e62330fcff73aa7b4e1904a08d92cbcf`.
Its source and all eight prior providers listed in the
[collection-rule receipt](parsons-specialize-root.md) were checked against
their frozen source snapshots at this build. Their object hashes are those
recorded there. Foundation/Mathlib and completeness objects remain an inherited
boundary, not a fresh independent transitive source audit.

This establishes the finite-bounding conversion under one positive Σ₁ side
guard. The complete strict Π₂ adapter, all cut-free sequent cases, the global
translation, and PRA witnessing remain open.

## Independent root replay

A third build at `/tmp/parsons-guarded-collection-build-2kx5qqwf` passed;
its source, object and complete-log hashes match both author runs. Its direct
specialization provider matches the independently rebuilt object accepted in
the prior review. The [independent artifacts](parsons-guarded-collection-replay/root-build/)
are preserved; the Foundation/Mathlib boundary remains inherited.
