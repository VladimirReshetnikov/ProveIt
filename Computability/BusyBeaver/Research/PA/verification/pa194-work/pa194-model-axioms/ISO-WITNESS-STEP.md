# Source successor application in the Q witness branch

`PA194IsoWitnessStepComponents.lean` proves typed identities for opening a closed two-variable template under the predecessor witness: the fresh witness is index 0 and the original target b becomes b+1. It uses these identities to match the opened witness's domain and successor components to the existing direct ordinal-step templates.

`isoWitnessStepProof` constructs a proof of shifted P(b+1) in the shifted witness context from explicit proofs of Q(c)(p), the direct ordinal-step formula for `shift c` in that witness context, and the domain of the target in that context. It derives the witness's domain, successor relation, and predecessor property using the previously checked constructors, and applies the direct ordinal-step proof. The arbitrary internal arity-one code c may be nonstandard. `isoWitnessStepProof_val` identifies the exact proof code, and `isoWitnessStepGraph_defined` gives one fixed Σ₁ graph in every candidate-PRA model with IΣ₁ arithmetic reduct.

The direct source ordinal-step and target-domain proofs remain explicit inputs. In particular, this is not yet the translated PA induction step, an existential-eliminated induction theorem, closed-formula environment independence, a native iPRA theorem, or machine correctness.

Run `bash check-iso-witness-step.sh REPO NEW_OUTPUT`. The new source is rebuilt in a fresh output against pinned prebuilt inputs, including the repository-replayed witness branch. This does not rebuild the full transitive source closure. Success includes six axiom reports with no `sorryAx`.
