# Vacuity at a label above the allocation range

`generalVacuity_all_codes` proves target vacuity at an independently chosen
label `x` for the positive translation of every internally valid source formula
`p`, including nonstandard Boolean and quantified syntax in candidate-PRA
models satisfying IΣ₁. The hypotheses require `base + p ≤ x`, initial bound
and free stack lookups through index `p` below `x`, and `x ≠ reserve`. The
quantifier cases use binder-context translation and target quantifier
commutation. A Σ₁-definable induction predicate tracks bounded model-valued
binder depth; a corollary covers the negative sequent translation.

This does not establish the current `ruleAllFresh` field with eigenlabel
`x = base`: the displayed bound generally fails and the translation may reuse
that label as an internal binder. An alpha-renaming or another argument remains
necessary. No complete compiler or consistency direction is established.
`check-general-vacuity.sh` replays the source closure and checks eleven axiom
reports. Retained objects and workspace foundations require their own provenance.
