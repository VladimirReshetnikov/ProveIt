# Checked partial truth over the universe

The unchanged
[`UniverseTruthZero`](Lean/BoundedZFCConsistency/UniverseTruthZero.lean)
passes a [local Lean check](results/universe-truth-zero-verification.json).
Under the explicit semantic axiom bundle, it defines quantifier-free truth
for arbitrary internal formula codes. Environments are internal functions
on the model's entire omega, with unrestricted set values. They therefore
cover nonstandard variable indices as well as external numerals.

The checked results establish total, single-valued truth certificates, the
six atomic and Boolean truth clauses, and the equivalence between
quantifier-free codehood and rank zero on formula codes. Quotation agrees
with ordinary satisfaction at the valuation induced by an internal
environment. The argument uses definable code induction with an explicit
formula witness; it assumes no external well-foundedness of internal codes.

Seventeen named axiom probes and nineteen typed callers pass with zero
warnings and only standard Lean axioms. Source and audit took 2.383 and
0.328 seconds with default proof limits, one thread, 4,096 MiB and a shared
120-second deadline. Seventeen project source/object pairs and Init are
reused from the actual [rank check](coded_rank_check.md). All 102 recorded
inputs remained unchanged after the audit. The
[publication](results/universe-truth-zero-publication.json) and
[history](universe-truth-zero/history.json.gz) preserve the exact source
snapshot, audit, dependency bindings and raw logs.

The unchanged
[`UniverseTruthLevel`](Lean/BoundedZFCConsistency/UniverseTruthLevel.lean)
also [passes](results/universe-truth-level-verification.json). Each external
natural number selects a separate object-language formula, with an exact
satisfaction specification. The positive levels have the stated Boolean
clauses, existential witnesses and universal counterexamples, and the
rank-guarded transitions between the two polarities. The inversion theorems
retain their previous-level alternatives. General collapse of levels and
consistency of positive-level certificates are later results; this module's
higher-level quotation transport is one-way and quantifier-free.

The Level check passes 33 named probes and 33 typed callers. Source and audit
took 3.068 and 0.413 seconds under the same default limits. Its 18 project
prerequisites plus Init come from the actual Zero check; all 113 recorded
inputs remained unchanged. The source has no warnings. The audit has 46
unused-variable-name warnings from named hypotheses in explicitly quantified
types; all callers typecheck and all axiom reports are standard. These
warnings are preserved in the [publication](results/universe-truth-level-publication.json)
and [history](universe-truth-level/history.json.gz).

Bounded derivation soundness, axiom truth and the final PA/240-state
consistency theorem remain later checks in this verification sequence.
