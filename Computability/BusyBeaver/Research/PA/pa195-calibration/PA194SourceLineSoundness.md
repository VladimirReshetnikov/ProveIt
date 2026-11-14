# Conditional soundness of numerical source proof lines

`PA194SourceLineSoundness.lean` proves a model-internal line-history theorem.
Let `lines` be an internally coded finite sequence, possibly of nonstandard
length. Assume each line is either a member of a chosen seed predicate, the
numerical modus-ponens conclusion of two earlier lines, or the numerical
universal-generalization conclusion of an earlier line. Assume also that the
positive translation of each seed is internally PA-provable. Then the
positive translation of every line is internally PA-provable.

The result holds for arbitrary nonstandard line codes, indices, and labels in
every nonempty candidate-PRA model with equality and an IΣ₁ arithmetic
reduct. It combines the already checked model-uniform MP and universal-rule
preservation results by IΣ₁ induction on a bounded Σ₁ prefix invariant. The
seed predicate is an arbitrary external predicate in the theorem; its
provability condition and the per-line validity condition are explicit
hypotheses. Lean reports `propext`, `Classical.choice`, and `Quot.sound` for
the printed theorem dependency, without `sorryAx`.

This is not yet a proof that the actual PA194 controller or machine execution
produces such a sequence, nor that the translations of its concrete axiom
families are internally PA-provable. It does not establish an iPRA theorem or
a PA194 machine/consistency implication.

Run `check-source-line-soundness.sh` with the audited `IPRA_LEAN_OVERLAY` and
`IPRA_FOUNDATION_OVERLAY` set; it rebuilds the dependencies in a fresh
temporary overlay and rejects `sorryAx`.

The full author replay and an independent full Linux replay both passed with
the audited overlays. An additional independent suffix replay recompiled the
final theorem using retained dependencies; no checked theorem used `sorryAx`.
