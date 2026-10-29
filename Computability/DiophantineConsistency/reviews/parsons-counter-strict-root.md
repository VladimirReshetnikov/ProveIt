# Counterexample case with a restricted strong hypothesis

`ParsonsCounterStrict.counter_strict_unbounded` handles the local induction
counterexample case with arbitrary finite positive Boolean Tree sides and
strict existential-prefix induction blocks over Σ₀ matrices. Its hypothesis
`BelowStrict H` only asks for translation of smaller cut-free derivations
whose marked contexts have those same side and block invariants. The original
existential conclusion must have height at most `H`.

The proof establishes that the three smaller base, step and negative cases
all retain the Tree invariant, that term rewriting preserves strictness, and
that the shifted remaining induction blocks retain strictness. It recursively
opens positive Boolean guard trees at arbitrary context positions and rebuilds
actual PA-minus rule proofs. This is a conditional local case: `BelowStrict H`
is not proved here, the base-shape invariant is not yet included in it, and no
reduction from arbitrary Σ₁ predicates to strict predicates is asserted.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`; both objects and complete logs match. The two
axiom reports list only `propext`, `Classical.choice`, and `Quot.sound`. The
[16-file replay manifest](parsons-counter-strict-replay/FILES.json) has
SHA-256 `a48d3f1fa5f68db69d68c489a7f0f25b49016c15c16eb4e88f30d79b55167d14`.
The direct StrictInvariant source hash
`e8f9c582dea832533e80f5a29d067f0cc507931a4f0347ec68c3c06719ad8f3d` and object
hash `6f3fb81ee258ac58d80ad88200fff07844174bf230a92964aeae73668d7672e2`
match its frozen provider. The other direct providers and hashes are the same
as in [the Tree counter-case receipt](parsons-counter-tree-root.md). Earlier
providers and Foundation/Mathlib are an inherited boundary, not a fresh
transitive source audit.

This theorem is not the global derivation induction, conservation theorem, or
the PRA-provability result. The separate HA theorem for the maintained
14-variable PDF equation is complete.

A third independent replay at `/tmp/parsons-counter-strict-build-ggbvjsy4`
passed with matching source, object and complete log hashes under the same
inherited-provider boundary.
