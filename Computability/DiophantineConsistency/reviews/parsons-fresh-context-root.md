# Fresh opening inside an arbitrary context

`ParsonsFreshContext.fresh_open_at` opens a selected universal at a fresh
variable after any finite prefix of the nonprincipal sequent. It shifts all
free variables, preserves cut-freeness, and produces a derivation strictly
below the original existential conclusion's height. It uses the occurrence
selection of `ParsonsAllInvert`; no permutation or contraction rule is added,
so selecting a later side does not consume the height margin.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`; both objects and complete logs match. The
axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`; the
bare prefix-selection lemma uses only `propext`. The [16-file replay
manifest](parsons-fresh-context-replay/FILES.json) has SHA-256
`b3162cde49fa5038c536ac472e4ec86ee4f3787006d218b60930479c09abf481`.
The direct `ParsonsAllInvert` source hash
`5ba857ee492335e85d94abab70b5a93434294af088afe58784d71937323e11a8`
matches its frozen snapshot, and its object hash is
`5d3ec89d2e4f17bca1995e3c58f245b295f8eb65ee15a4388b28bc4acb0151c0`.
Earlier provider chains, Foundation/Mathlib, and completeness objects remain
an inherited boundary, not a fresh transitive source audit.

This is a cut-free source transformation only; the global recursion, general
Π₂ normalization, conservation and the PRA-provability target remain open.
The maintained 14-variable PDF equation's HA theorem is complete separately.

A third independent replay at `/tmp/parsons-fresh-context-build-z0h6cyor`
passed with matching source, object and complete log hashes under the same
inherited-provider qualification.
