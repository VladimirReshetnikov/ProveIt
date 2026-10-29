# Counterexample case under the full restricted invariant

`ParsonsCounterStable.counter_stable_unbounded` proves the local induction
counterexample case for any finite marked context whose sides carry positive
Boolean Tree descriptors, whose induction blocks use strict existential-prefix
Σ₁ predicates, and whose base states carry actual-axiom shape certificates.
Its `BelowStable H` hypothesis asks for translation of strictly smaller
cut-free derivations **only when all three invariants hold**. The original
existential conclusion must have height at most `H`.

The proof preserves all three invariants across arbitrary ∀/∨/∧ guard opening,
term rewriting, and the three base, step, and negative induction cases. It
recurses on additive formula-node count while retaining the source proof-height
bound and constructs actual PA-minus rule proofs. This is a conditional local
case; `BelowStable H` and the full well-founded derivation induction are not
proved in this file. The restriction to strict induction predicates remains.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`; both objects and complete logs match. The two
axiom reports list only `propext`, `Classical.choice`, and `Quot.sound`. The
[16-file replay manifest](parsons-counter-stable-replay/FILES.json) has
SHA-256 `be1d251ddb2f30b27e5696f4706f5e6c5fe5fb7a64e9a26d5df94aaa13ae7bc0`.
The direct BaseInvariant source hash
`575f3b40eecc4d4ff481cc33608a561c642ae5d9b8728e80f182aa17afe2b098` and object
hash `c035e77286aa099d9ee826b18408be074d8b68780e22b2c66d994b7d236264a3`, and
the StrictInvariant source hash
`e8f9c582dea832533e80f5a29d067f0cc507931a4f0347ec68c3c06719ad8f3d` and object
hash `6f3fb81ee258ac58d80ad88200fff07844174bf230a92964aeae73668d7672e2`,
match their frozen providers. Other direct providers are as in [the Tree
counter-case receipt](parsons-counter-tree-root.md). Earlier provider chains,
Foundation/Mathlib, and completeness objects are inherited, not a fresh
transitive audit.

This is not the global derivation induction, full Σ₁ conservation, or the
PRA-provability result. The separate HA theorem for the maintained
14-variable PDF equation is complete.

A third independent replay at `/tmp/parsons-counter-stable-build-5zqwfpdg`
passed with matching source, object and complete log hashes under the same
inherited-provider boundary.
