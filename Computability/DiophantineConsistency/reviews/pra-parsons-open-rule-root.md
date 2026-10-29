# Candidate PRA and the Parsons open induction rule

`PRAParsonsOpenRule.parsons_open_induction_rule` connects the candidate PRA
open induction rule to the actual `ParsonsRule.base` and `ParsonsRule.step`
formulas, retaining arbitrary universally closed parameters. It does not
assert admissibility of the Σ₁ induction rule or PRA conservation.

The independent replay `/tmp/pra-parsons-open-root-hjk05_br` passed both
modules without warnings, matched the author object hashes, and reported only
`propext`, `Classical.choice`, and `Quot.sound`. It used the independently
replayed candidate induction rule and ParsonsRule/ParsonsGuard objects.
Foundation, Mathlib, PRATheory and earlier providers remain inherited cache
boundaries. The [evidence packet](pra-parsons-open-rule-root-replay/)
preserves the author and independent runs.
