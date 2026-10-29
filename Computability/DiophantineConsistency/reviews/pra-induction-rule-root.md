# Candidate PRA parameterized open induction rule

`PRAInductionRule.open_induction_rule` shows that from candidate-PRA proofs
of the universally closed base and step for an open matrix, candidate PRA
proves the universally closed induction conclusion, with arbitrary free
parameters retained. The argument uses the actual candidate induction schema
in arbitrary equality models and first-order completeness. It concerns
open formulas, not the Σ₁ induction rule used in Parsons conservation.

The independent replay `/tmp/pra-induction-rule-root-prh6h3dr` passed both
modules without warnings and matched author objects; the axiom report uses
only `propext`, `Classical.choice`, and `Quot.sound`. The open-induction
provider was independently replayed. Foundation, Mathlib, PRATheory and
earlier code providers remain inherited cache boundaries. The
[evidence packet](pra-induction-rule-root-replay/) preserves the author run.
