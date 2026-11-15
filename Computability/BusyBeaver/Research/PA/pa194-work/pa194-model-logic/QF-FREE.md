# Quantifier-free universal compiler rule

`quantifierFree_freeBridge` proves the source-freeing and target-translation
code equality for valid internally quantifier-free formulas, using internal
Σ₁ structural induction and allowing nonstandard model-valued codes and
environments. `simRuleAll_quantifierFree` derives the exact universal-rule
implication from the source sequent validity and membership premises, without
an admission assumption.

Quantified descendants, a complete simulation, PA identification and both
machine/consistency directions remain open. `check-qf-free.sh` replays the
source closure and checks two axiom reports; retained objects and workspace
foundations require their own provenance.
