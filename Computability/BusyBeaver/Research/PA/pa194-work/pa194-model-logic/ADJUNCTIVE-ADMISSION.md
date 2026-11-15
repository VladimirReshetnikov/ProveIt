# Admission for adjunctive theory axioms

The upstream `adjunctiveTheory` consists of five equality axioms and weak
adjunction, with an explicit Δ₁ axiom presentation. The ranked and seeded
`simRuleAdjunctiveAxiom` theorems derive its numerical axiom-field conclusion
for every internal axiom code from the corresponding admission at an `axm`
node. The admission supplies the required reserve bound. Models satisfy PRA
and IΣ₁, and codes may be nonstandard.

This does not identify the theory with PA, construct a complete simulation,
or prove a machine/consistency implication. `check-adjunctive-admission.sh`
replays the source closure and checks two axiom reports; retained objects and
workspace foundations require their own provenance.
