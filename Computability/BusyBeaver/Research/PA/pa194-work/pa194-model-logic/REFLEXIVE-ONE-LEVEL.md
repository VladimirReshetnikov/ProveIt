# Seeded freshness with reflexive equality

`simRuleAllFresh_oneLevelReflexiveSeed` proves the target eigenlabel-vacuity
implication required by `CutValidity.Sim.ruleAllFresh` for formulas satisfying
`OneLevelReflexive`, under the actual seeded admission and source-sequent
premises in models of PRA and IΣ₁. Codes and environments may be nonstandard.

The internal Π₁ condition requires each reached quantifier body to be
quantifier-free and every equality atom in that body to have the same term code
in both argument slots. Boolean structure and positive or negative membership
and reflexive equality atoms are allowed inside binders; mixed equality may
occur outside them. An internal Σ₁ induction proves binder-label transport.
The code also proves inclusion of the earlier membership-only class and gives
a strict code example.

Nested binders and mixed equality inside binder bodies remain outside this
class. This is a partial compiler field, not a complete compiler or a
consistency direction. `check-reflexive-one-level.sh` replays the source closure
and checks 21 axiom reports; retained objects and workspace foundations require
their own provenance.
