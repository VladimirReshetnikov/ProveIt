# Atomic existential compiler cases using neighborhood witnesses

The upstream `PA194ModelNeighborhoodWitness` theorem derives target
primitive-to-neighborhood equality and the required existential introductions
from explicit reserve-label inequalities, without the earlier primitive
equality-vacuity premise. It applies in PRA models satisfying IΣ₁.

`PA194ModelExEqualityWitness` obtains those inequalities from
`RankedAdmission`. `simRuleExs_positiveRelation_fresh` and its negative
counterpart then establish the exact `ruleExs` implication for every valid
relational atom and legal closed substitution term, with arbitrary internal
arity, relation and vector codes, including nonstandard inputs. The source
sequent validity and membership assumptions are explicit.

This discharges the isolated equality-vacuity premise for atomic `ruleExs`;
it does not prove primitive-equality vacuity, handle compound or quantified
substitution, or construct the complete compiler or a consistency direction.
`check-ex-atom-witness.sh` replays the source closure and checks fifteen axiom
reports. Retained objects and workspace foundations require their own provenance.
