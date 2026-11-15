# Freshness for quantified membership atoms

The exact `ruleAllFresh` implication is proved for a sequent formula consisting
of one universal or existential quantifier over any internally valid positive
or negative binary membership atom, with arbitrary model-valued vector codes.
The proof handles either or both bound-variable occurrences and free-only
arguments. It assumes the source sequent premises, `RankedAdmission`, and an
empty initial bound stack. Target alpha conversion uses membership congruence,
vacuity, specialization and quantifier commutation; existential cases use
contraposition and double-negation elimination.

Arbitrary nested quantifiers and quantified equality bodies are not covered.
The result does not construct a complete compiler or either consistency
direction. `check-atomic-alpha.sh` replays the closure and checks ten axiom
reports. Retained objects and workspace foundations require their own provenance.
