# Recursive invariant for induction parameter blocks

`ParsonsBlock.State` records an arbitrary simultaneous term substitution into
the actual normalized induction body, indexed by the number of bound
parameters that remain. `start` establishes the state for the normalized
IΣ₁ output; `opening` gives the exact principal existential witness instance;
`step` updates the state after that witness; and `finish` shows that a state
with no parameters left is exactly an existential counterexample matrix for a
term-rewritten induction formula. The construction allows arbitrary terms
and keeps any remaining bound parameters explicit.

`principal_parameter` implements the parameter-block existential case of a
height recursion. It applies its explicit recursive hypothesis to the actual
cut-free witness premise, with the updated state and a height strictly below
that of the enclosing existential inference. This comparison is entirely
inside the already cut-free derivation; no comparison across the earlier
cut-elimination step is used. The recursive hypothesis remains a local
assumption, not an axiom or a proof of the complete recursion.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`. Both objects and complete logs match. Six
axiom reports contain no axioms beyond `propext`, `Classical.choice`, and
`Quot.sound`; the outer-closure identity has no axiom dependencies. The
[16-file replay manifest](parsons-block-replay/FILES.json) has SHA-256
`0a3358b3ace5efb0625b906a8d5b5b67486560182449b9483d3dc4e5f847b34e`.
Direct prerequisites were previously built `ParsonsOpened` and its prior
providers; Foundation/Mathlib objects are an inherited boundary, not a fresh
transitive source audit. Scratch attempts around dependent index arithmetic
and substitution composition failed before being fixed; their console logs
were not retained.

This completes the invariant and principal existential transition for a
partially opened parameter block. It does not cover arbitrary intervening LK
rules, prove the full cut-free translation, supply strict Π₂ side normalization,
or establish the PRA witnessing theorem.

A third independent replay at `/tmp/parsons-block-build-j47_7mx5` matched
both source and object hashes and full logs of the author builds. All 16
author-manifest entries matched. The direct opened-parameter provider matches
its independently replayed object. The [independent replay](parsons-block-independent-replay/)
has the same inherited Foundation/Mathlib boundary.
