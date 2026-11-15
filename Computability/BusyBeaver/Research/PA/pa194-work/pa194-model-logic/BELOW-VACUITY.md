# Vacuity below the binder allocation base

`generalVacuity_below_all_codes` proves target vacuity at `x` for every
internally valid source formula in candidate-PRA models satisfying IΣ₁,
including nonstandard formulas and depths. Its hypotheses are `x < base`,
initial bound and free stack lookups through the root code distinct from `x`,
and `x ≠ reserve`. A bounded-depth Σ₁ induction shows new binder labels avoid
`x` and propagates vacuity through source constructors.

`shiftedBase_vacuity` applies this to the current base with binder allocation
starting at `base + 1`, ranked admission and an empty bound stack. This does not
establish `ruleAllFresh`: the current translation starts at `base`, and its
target-provable equivalence with the shifted translation remains open.
`simRuleAllFresh_of_baseShift` reduces the current eigenlabel-vacuity field to
explicit target-provable implications in both directions between these two
translations. Those implications remain unproved. `check-below-field.sh`
replays this stronger reduction and checks four axiom reports.
`check-below-vacuity.sh` replays the source closure and checks six axiom
reports. Retained objects and workspace foundations require their own provenance.
