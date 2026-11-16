# Conditional existential introduction for equality atoms

`simRuleExs_equalityCode_of_eqVacuity` and its negative counterpart prove the
exact existential compiler implication for arbitrary internally valid binary
equality-atom codes and legal source terms, assuming `RankedAdmission` and the
target premise `eq(termLabel,base) → ∀reserve eq(termLabel,base)`. The results
include nonstandard model-valued syntax and combine free-only and diagonal
cases with mixed-occurrence cases.

The primitive-equality vacuity premise is not established here. Compound and
quantified bodies, a complete compiler, and both consistency directions remain
open. `check-ex-equality-code.sh` replays the source closure and checks seven
axiom reports. Retained objects and workspace foundations require their own
provenance.
