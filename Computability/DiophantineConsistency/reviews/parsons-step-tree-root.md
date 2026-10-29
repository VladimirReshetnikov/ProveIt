# Guard descriptors for strict induction sides

`ParsonsStepTree.strict` proves that the *original* step side
`∀x (φ(x) → φ(x+1))` has a positive Boolean tree descriptor when
`φ = ∃y D(x,y)` and `D` is Σ₀, with arbitrary free parameters. The proof
opens the step universal and recognizes the negative existential as a
universal with bounded negated matrix. `strict_negative` gives the same kind
of descriptor for the negative counterexample side at an arbitrary witness
term. `bounded` handles Σ₀ induction predicates, and
`neg_bounded_exists` is a reusable sublemma.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`; both objects and complete logs match. The
axiom reports list only `propext`, `Classical.choice`, and `Quot.sound`. The
[16-file replay manifest](parsons-step-tree-replay/FILES.json) has SHA-256
`d29caff37c22867df72968cd6ff5d73f3776a3100a12c9ae51c0086b8dc0cf73`.
The direct `ParsonsGuardTree` source hash
`409662779f56e90637900537dfbc78276f87362eb30f9a520c6aaf2f33e5b9c0`
matches its frozen snapshot, and its object hash is
`9deaab2f8a25685a1c4fa7b564a68335529bcf93bc704f1d7ae4c55916621d7c`.
Earlier providers and Foundation/Mathlib are an inherited boundary, not a
fresh transitive source audit.

The predicate restriction is material: these lemmas do not classify every
Foundation Σ₁ formula or solve bounded-quantifier normalization. They do not
prove the global induction, conservation, or PRA-provability of the target.
The HA theorem for the maintained 14-variable PDF equation is complete
separately.

A third independent replay at `/tmp/parsons-step-tree-build-994zsvko` passed
with matching source, object and complete log hashes under the same inherited
provider boundary.
