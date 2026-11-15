# Quantifier-free seeded freshness rule

The internally coded quantifier-free predicate has its expected constructor
characterization for arbitrary model-valued syntax: each leaf satisfies it,
conjunction and disjunction satisfy it exactly when both children do, and
neither quantifier constructor satisfies it. The Boolean converses decompose
nonstandard coded descendant chains at their first edge.

`simRuleAllFresh_quantifierFreeSeed` proves the exact
`CutValidity.Sim.ruleAllFresh` implication for each internally quantifier-free
sequent formula under `SeedAdmission 0 reserve e (allIntro s p d)` and the
source sequent premises. A Σ₁ structural induction shows that translation at
`base` and `base + 1` agrees for these formulas, discharging the conditional
base-shift premises. The results hold in candidate-PRA models satisfying IΣ₁,
including for nonstandard source and chain codes.

The predicate is explicitly defined by coded descendants; equivalence to a
separately named Foundation QF predicate is not claimed. Formulas containing
quantifiers, a complete compiler, and both consistency directions remain open.
`check-qf-seed.sh` replays the source closure and checks seven axiom reports.
Retained objects and workspace foundations require their own provenance.
