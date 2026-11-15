# Existential introduction for atomic source formulas

`simRuleExs_positiveAtomCode` and `simRuleExs_negativeAtomCode` prove the
existential compiler implications for arbitrary internally valid source
relation and vector codes and legal terms under `RankedAdmission`. An extra
primitive-equality vacuity premise is required only when the source relation is
equality. The statements cover candidate-PRA models satisfying IΣ₁, including
nonstandard syntax.

The equality premise is not established in general. A special case follows
when the reserved label equals the primitive equality formula code, but that
term-dependent reserve does not solve the fixed-reserve compiler obligation.
Compound and quantified bodies, the full compiler, and both consistency
directions remain open. `check-ex-atom-unified.sh` replays the source closure
and checks four axiom reports; retained objects and workspace foundations
require their own provenance.
