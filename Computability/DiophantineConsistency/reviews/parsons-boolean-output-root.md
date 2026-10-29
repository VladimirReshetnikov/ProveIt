# Reconstructing Boolean sides in the rule calculus

`ParsonsBooleanOutput.collapse_or` turns an actual rule proof with `P` and `Q`
as separate disjunctive side occurrences into one with `P ∨ Q` at the same
context position. `collapse_and` combines actual rule proofs for the two
branches into one with `P ∧ Q` there. Arbitrary finite prefix and suffix
contexts are preserved. The logical implications use equality-model
completeness and are noncomputable in the Lean metatheory.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`; both objects and complete logs match. The
axiom reports list only `propext`, `Classical.choice`, and `Quot.sound`. The
[16-file replay manifest](parsons-boolean-output-replay/FILES.json) has SHA-256
`b24401916d880ce35b14dc82042befb93ea970018311998d62209ffe97086ad6`.
The direct `ParsonsStructure` source hash
`d9e2735b67c4b01fb1aea0d223bcf194c800d8fa29673078634ef0d095876c83` and object
hash `e6a4bf7137288fda68f43d21f6a0155aae37b62acd17dd92f665e988f070ea80`
are inherited from the earlier compiled provider. Foundation and package
objects are also inherited, not a fresh transitive source audit.

This rule-output helper does not itself establish source normalization,
global recursion, conservation, or the PRA-provability target. The separate
HA theorem for the maintained 14-variable PDF equation is complete.

A third independent replay at `/tmp/parsons-boolean-output-build-pcopnni3`
passed with matching source, object and full-log hashes under the same
inherited-provider boundary.
