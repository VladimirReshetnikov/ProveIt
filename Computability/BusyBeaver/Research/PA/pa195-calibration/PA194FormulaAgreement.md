# Candidate formula closer agrees with internal traversal

`PA194FormulaAgreement.lean` proves that the explicit candidate-PRA formula
closer in `PA194FormulaUpdate.lean` agrees with the Foundation internal formula
traversal in `PA194InternalFormulaClose.lean`. The agreement applies in every
nonempty candidate-PRA model with equality interpreted as equality and an
IΣ₁ arithmetic reduct. The label, syntax code, and binder depth can all be
nonstandard model elements; the source code must be an internally well-formed
arithmetic formula at the given depth.

The key theorem `budget_agree` fixes a label and a ceiling `c`. For every
formula code `p` at depth `d`, it proves agreement for every budget `b` with
`b ≤ c`, `p ≤ b`, and `b + d = c`. The proof uses Foundation's Σ₁ structural
induction with a bounded universal over the budget. Boolean children have
smaller formula codes and keep the budget; a quantified body's code is smaller
and its budget decreases by one, so its depth increases by one while the
ceiling stays fixed. The positive-budget requirement follows from `p ≤ b`
because a quantified formula code is positive. The root wrapper takes
`b = p` and `c = p + d`, so its chosen budget is sufficient. The proof handles
all these inequalities inside arbitrary models, including nonstandard values.

`root_agree` proves the result for the `Code 3` wrapper at arbitrary initial
depth. `compiler_close_agree` proves it for the compiler-interface `Code 2`
at depth zero, retaining the two pairing-projection certificates as explicit
hypotheses. `canonical_close_agree` fixes certified projections once and for
all, eliminating these hypotheses, and `canonical_close_wellformed` establishes
that its output is an internal arithmetic formula at depth one. The Lean
axiom report for these theorems lists only `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorryAx`.

This identifies the named-variable closing component. It does not by itself
prove that the source compiler produces correct formulas, that the machine
searches exactly those formulas, or either direction of the PA194
machine/refutation equivalence. Run `check-formula-agreement.sh` with the
audited `IPRA_LEAN_OVERLAY` and `IPRA_FOUNDATION_OVERLAY` set; it builds all
comparison dependencies in a fresh temporary overlay.

An independent fresh Linux replay of `check-formula-agreement.sh` also passed
with the audited overlays, rebuilding all local comparison dependencies and
checking the displayed theorem axioms for `sorryAx`.
