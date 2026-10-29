# Counterexample case for positive Boolean guard trees

`ParsonsCounterTree.counter_tree_unbounded` handles the local induction
counterexample case for an arbitrary finite marked context whose side entries
carry `ParsonsGuardTree.Tree` descriptors: finite positive Boolean trees of
universal prefixes and Σ₁ leaves. Base and induction-block entries may appear
anywhere. It opens ∀, ∨, and ∧ occurrences directly in the original cut-free
source derivation without consuming the height margin, recursively decreases
an additive logical-node count, applies the Σ₁-side induction-rule case, and
reconstructs actual PA-minus rule proofs.

The theorem explicitly assumes `Below H`: every marked cut-free derivation of
height below `H` has already been translated to a rule proof. The original
existential conclusion must have height at most `H`. The side descriptors are
also assumptions. Neither the strong derivation induction nor descriptors for
arbitrary Foundation Π₂ formulas are proved here; bounded quantifiers and
non-prenex induction predicates require further analysis. These restrictions
remain even though a separate theorem constructs descriptors for the step and
negative sides of strict Σ₁ induction predicates.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`; both objects and complete logs match. Both
axiom reports list only `propext`, `Classical.choice`, and `Quot.sound`. The
[16-file replay manifest](parsons-counter-tree-replay/FILES.json) has SHA-256
`81591c1486b4374dba46f10adffa95c0fa4e058b561d1ef452377c0081ea406d`.
Direct provider source and object hashes, in import order, are:

- `ParsonsGuardTree`: `409662779f56e90637900537dfbc78276f87362eb30f9a520c6aaf2f33e5b9c0`, `9deaab2f8a25685a1c4fa7b564a68335529bcf93bc704f1d7ae4c55916621d7c`.
- `ParsonsFreshContext`: `7c1f040a6c590948337157d71c1e9238ddca37258614a7416d44beaef9f83cd7`, `c9aada04e471738fc448705119707978c9cc9eddc3a6b30f78a3a8b3da854b53`.
- `ParsonsOrInvert`: `7b7bdae77541150206d92c52c019539daf40b135d1fcdc80879f43604f157fe0`, `0c682f269e62dea65e246961fa15782bae31f52d9e24fa879655349df892297b`.
- `ParsonsAndContext`: `d6dfb26c37f68ff4d57a80a371236c5cac8e980154a2520b78121705e8f09e2f`, `79f1d45b2b06ca956975455f2893cb4761df40a03bc957815efb48169ede84df`.
- `ParsonsBooleanOutput`: `541ca672d6ee25ab12e2eeb05df7f50002adc910f908fec9876d2c08bfb4adb7`, `de9ed348145095035bc339afdadd612365344fc44846fa7c02be1ee352702850`.

Each source matches its frozen snapshot. Earlier provider chains,
Foundation/Mathlib, and completeness objects are an inherited boundary, not
a fresh transitive audit. This is the conditional local case, not the global
recursion, conservation theorem, or PRA-provability result. The separate HA
theorem for the maintained 14-variable PDF equation is complete.

A third independent replay at `/tmp/parsons-counter-tree-build-53nta8o0`
passed with matching source, object and complete log hashes under the same
inherited-provider boundary.
