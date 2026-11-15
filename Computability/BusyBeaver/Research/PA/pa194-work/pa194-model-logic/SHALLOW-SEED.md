# Seeded freshness for shallow membership formulas

The exact `CutValidity.Sim.ruleAllFresh` implication holds under
`SeedAdmission 0 reserve e (allIntro s p d)` for sequent formulas satisfying
`ShallowMembership`. This explicit Π₁ condition requires each quantified node
reachable by a coded source constructor chain to have a positive or negative
membership-atom body. It includes arbitrary Boolean structure around these
one-quantifier atoms and all quantifier-free formulas, including nonstandard
model-valued source codes. A Σ₁ structural induction uses target alpha
conversion for both quantifiers, both polarities and every argument pattern.

The development also checks the predicate's Boolean and quantifier constructor
characterization on nonstandard coded chains. It does not identify the predicate
with a separately named Foundation class. Nested quantifiers, quantified equality
or compound bodies, the remaining compiler fields, and both consistency
directions remain open. `check-shallow-seed.sh` replays the closure and checks
twelve axiom reports; retained objects and workspace foundations require their
own provenance.
