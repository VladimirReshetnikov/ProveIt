# Seeded freshness for one-level membership formulas

`simRuleAllFresh_oneLevelSeed` establishes the exact target eigenlabel-vacuity
implication required by `CutValidity.Sim.ruleAllFresh` for each sequent formula
`q` satisfying `OneLevelMembership q`, under the source sequent premises and
`SeedAdmission 0 reserve e (allIntro s introBody d)`. The predicates are
internal Π₁ properties, and Σ₁ structural inductions cover arbitrary
model-valued codes, including nonstandard codes.

Each quantified descendant of `q` must have an internally quantifier-free,
membership-only body. Arbitrary conjunction and disjunction are permitted
both outside quantifiers and inside their bodies; equality atoms may occur
outside binders. Characterization theorems check the Boolean and quantifier
constructors and membership atoms. The quantified cases derive label renaming
from target membership congruence and below-label vacuity.

Nested quantifiers, equality atoms inside quantified bodies, the remaining
compiler rules, and both consistency directions remain open.
`check-one-level-seed.sh` replays the source closure and checks twenty axiom
reports. Retained objects and workspace foundations require their own provenance.
