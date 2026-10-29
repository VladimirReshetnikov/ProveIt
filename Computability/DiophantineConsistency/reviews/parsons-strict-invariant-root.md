# Strict induction-block invariant

`ParsonsStrictInvariant.Strict` describes a finite existential prefix over a
Σ₀ matrix. `rewrite` proves that strictness survives the term substitution
actually used in counterexample elimination. The original base, step, and
negative sides of a strict induction predicate all have Tree descriptors.
`StrictBlocks` records strictness for every marked induction block, and is
preserved by eigenvariable shifts and the duplicate-safe contraction selection.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`; both objects and complete logs match. The six
axiom reports list only `propext`, `Classical.choice`, and `Quot.sound`. The
[16-file replay manifest](parsons-strict-invariant-replay/FILES.json) has
SHA-256 `764c7a0900274ec760ed4e4a4b2e43934f1be639c080308b5af7c8bd8a0512f4`.
The direct StrictPrefixTree source hash
`a6bd711242b19d4aaf3d321aebb392c8a67beb67d0fb04b4aa71fb100fdbda00` and
object hash `94cc735011c02bdbd9c7166c79e05a5d65a78072138bca6ac4cc6adf5f81504b`
match the frozen provider. Earlier providers and Foundation/Mathlib are an
inherited boundary, not a fresh transitive audit.

Strictness is an explicit restriction: this file does not reduce arbitrary
Σ₁ induction to strict induction, establish the global induction, or prove
conservation or the PRA-provability target. The separate HA theorem for the
maintained 14-variable PDF equation is complete.

A third independent replay at `/tmp/parsons-strict-invariant-build-yjz0tmon`
passed with matching source, object and complete log hashes under the same
inherited-provider boundary.
