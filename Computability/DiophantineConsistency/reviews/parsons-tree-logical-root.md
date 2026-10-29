# Tree descriptors through the logical derivation cases

`ParsonsTreeLogical` proves that marked Tree-side contexts remain valid when
an ordinary principal ∨, ∧, ∀, or ∃ formula is replaced by the actual
cut-free rule premise(s). The ∀ case shifts every other marked entry and the
∃ case accepts an arbitrary witness. `good_select` also preserves descriptors
for the actual duplicate-safe premise selection used by contraction.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`; both objects and complete logs match. All
five axiom reports list only `propext`, `Classical.choice`, and `Quot.sound`.
The [16-file replay manifest](parsons-tree-logical-replay/FILES.json) has
SHA-256 `c48ef4051840c1a12f6a0fb4f03e075a7a39a3d3ae8fc993b72e5651c61c3c07`.
The direct GuardTree source hash
`409662779f56e90637900537dfbc78276f87362eb30f9a520c6aaf2f33e5b9c0` and
object hash `9deaab2f8a25685a1c4fa7b564a68335529bcf93bc704f1d7ae4c55916621d7c`
match the frozen provider. Earlier providers and Foundation/Mathlib are an
inherited boundary, not a fresh transitive audit.

This preserves an assumed invariant; it does not establish the induction-block
or shaped-base cases, the global recursion, or the PRA-provability target.
The separate HA theorem for the maintained 14-variable PDF equation is complete.

A third independent replay at `/tmp/parsons-tree-logical-build-jofja1ye`
passed with matching source, object and complete log hashes under the same
inherited-provider boundary.
