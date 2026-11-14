# PA194 source term shift in all IΣ₁ models

The PA194 source language has no function symbols, including inside
nonstandard arithmetic models. `term_cases` proves that every internally valid
source term is internally a bound variable or a free variable. From this,
`termShiftAlgorithm_correct` proves that an explicit arithmetic algorithm
using predecessor, pair projections, and a conditional equals Foundation's
internal `termShift language` on **every internally valid term**, including
nonstandard terms, in every model of IΣ₁.

`validTermShiftGraph` is a fixed parameter-free Σ₁ formula describing the
two variable cases. `validTermShiftGraph_iff` proves that, on every internally
valid input in every such model, its output relation is exactly the internal
term-shift function. `termShiftAlgorithm_nat` independently identifies the
algorithm on all natural-number inputs with the earlier proved primitive-
recursive `PA194TermShiftPR.termShiftCode`.

The repository source file passes its ordered local dependency-overlay check.
The printed theorems depend on `[propext, Classical.choice, Quot.sound]` and do
not depend on `sorryAx`. An independent full nested standalone replay also passed from a fresh tmpfs
directory using the audited Foundation overlay.

These are model-uniform term-level results. They do not identify the chosen
candidate-PRA function symbol's interpretation with the algorithm on
nonstandard inputs, establish full formula-shift or compiler correctness in
arithmetic, or prove a PA194 machine/Con(PA) implication. The graph agreement
requires its input to satisfy the internal source-term recognizer.

To rebuild from the repository root, set `IPRA_FOUNDATION_OVERLAY` to the
audited current Foundation object overlay and run
`bash Computability/BusyBeaver/Research/PA/pa194-source-term-shift-model/check.sh`.
