# Freshness for quantified diagonal equality

The four `simRuleAllFresh_*EqualityDiagonal` theorems prove the target
eigenlabel-vacuity field for `∀x (x = x)`, `∃x (x = x)`, `∀x (x ≠ x)`, and
`∃x (x ≠ x)`. They hold for arbitrary model-valued environments without seeded
admission or the unproved primitive-equality-vacuity premise. The proof uses
target derivability or refutability of observational equality reflexivity.

These cases do not establish mixed equality, general quantified substitution,
a complete compiler, or either consistency direction. `check-diagonal-seed.sh`
replays the source closure and checks four axiom reports. Retained objects and
workspace foundations require their own provenance.
