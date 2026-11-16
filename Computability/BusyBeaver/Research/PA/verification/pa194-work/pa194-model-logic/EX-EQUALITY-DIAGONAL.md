# Existential introduction for diagonal equality

`targetExists_of_bodyTheorem` derives target existential closure of any
target-provable formula using the nonempty-domain equality axiom, without a
label-vacuity assumption. The exact existential compiler implication is proved
for the positive and negative source equality bodies `#0 = #0`, for every legal
source term and arbitrary model parameters, without freshness or admission
assumptions. The proof uses reflexivity of numerical observational equality and
checks the source substitutions and translated code identities.

Mixed bound/free equality atoms and compound or quantified bodies remain open;
these results do not construct a complete compiler or either consistency
direction. `check-ex-equality-diagonal.sh` replays the source closure and
checks nine axiom reports. Retained objects and workspace foundations require
their own provenance.
