# Quantifier-free existential compiler rule

`simRuleExs_quantifierFreeRankedFull` proves the exact existential compiler
implication for every valid internally quantifier-free body, with arbitrary
Boolean structure, relation atoms, legal closed substitution terms and
nonstandard codes. It assumes the source sequent premises and `RankedAdmission`
at the existential node in models of PRA and IΣ₁; the initial bound stack may
be arbitrary and no primitive-equality-vacuity assumption is needed.

Two internal Σ₁ inductions prove substitution/translation correctness and
that a valid one-variable quantifier-free body ignores the tail of its bound
environment. Quantified bodies, the remaining compiler fields, PA identification
and both machine/consistency directions remain open. `check-qf-ranked-ex.sh`
replays the source closure and checks three axiom reports. Retained objects
and workspace foundations require their own provenance.
