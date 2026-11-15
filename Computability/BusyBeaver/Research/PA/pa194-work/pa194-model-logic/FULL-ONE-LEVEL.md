# Seeded freshness for one-level formulas

`simRuleAllFresh_oneLevelQFSeed` proves the exact eigenlabel-vacuity
implication required by seeded `CutValidity.Sim.ruleAllFresh` for source
sequent formulas satisfying `OneLevelQF`, under the actual seeded admission
and source-sequent premises in models of PRA and IΣ₁. Codes and environments
may be nonstandard.

The internal Π₁ class requires every reached binder to have a quantifier-free
body. It permits arbitrary Boolean structure outside and inside binders and
all positive and negative source relation atoms, including mixed equality
involving the bound variable. Internal Σ₁ induction proves binder-label
transport. Mixed equality uses the upstream primitive-to-neighborhood theorem
and neighborhood transitivity, with reserve freshness supplied by admission.

Nested binders, the remaining compiler rules, and both consistency directions
remain open. `check-full-one-level.sh` replays the source closure and checks
fifteen axiom reports. Retained objects and workspace foundations require
their own provenance.
