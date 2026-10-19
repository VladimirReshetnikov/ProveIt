# Checked internal ZFC axiom codes

The unchanged [`AxiomCode`](Lean/BoundedZFCConsistency/AxiomCode.lean)
passes a [local Lean check](results/axiom-code-verification.json). Its
internal predicate recognizes seven fixed axiom quotations and Separation
and Replacement instances whose parameters range over internal formula
codes. The schema constructors preserve codehood and agree with quotation
on external formulas. Their formulas have exact satisfaction specifications
in arbitrary models of the explicit semantic axiom bundle.

`conZFCForm n` rules out a coded derivation of falsity whose context consists
of internal ZFC axiom codes and whose formula occurrences satisfy the bound
at the external numeral `n`. The check establishes this characterization
and the conditional completeness bridge. It does not discharge the
all-model no-refutation hypothesis; truth of the axioms and bounded
soundness come later. Only forward quotation soundness is asserted here;
the source's prose about strictness in nonstandard models is not a checked
converse or strictness theorem.

Twenty named axiom probes and twenty typed callers pass with zero warnings
and only standard Lean axioms. Source and audit took 1.946 and 0.298 seconds,
with one thread, 4,096 MiB and a shared 120-second deadline. The source's
existing recursion limit of 8,000 is retained; audit proof limits are
defaults. Its local opacity declaration for `sealF` matches the source.
Seventeen project source/object pairs and Init are reused from the actual
successful [rank check](coded_rank_check.md), with all 101 recorded inputs
unchanged after the audit.

The [publication record](results/axiom-code-publication.json) and
[history](axiom-code/history.json.gz) retain the exact audit, dependency
bindings, reviewed guard and raw logs. This check adds no external-model
existence assertion or final PA/240-state consistency theorem.
