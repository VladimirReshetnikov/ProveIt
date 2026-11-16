# Source successor property with premises in the original context

`PA194IsoSuccessorSuppliers.lean` removes the two shifted witness-context premises of the previous successor-property construction. From a Q guard it projects the target's domain, checks its exact shift to the target-domain template, and weakens that proof into the witness context. It also shifts and weakens an explicit direct source ordinal-step proof into the witness context.

`isoSuccessorSuppliedProof` therefore constructs P(c)(b) in an arbitrary original source context from explicit proofs in that context of Q(c)(p), successor(p,a), the guard `domain(b) ∧ orderIso(a,b)`, the fixed universal predecessor-matching theorem, and the direct ordinal-step formula for c. The internally valid arity-one code c can be nonstandard. The proof code has one fixed Σ₁ graph (`isoSuccessorSuppliedGraph_defined`), and `isoSuccessorSuppliedProof_val` checks the exact constructed code in every candidate-PRA model with IΣ₁ arithmetic reduct.

The direct source ordinal-step proof remains an explicit input, as do the guard, Q premise, matching theorem and successor premise. In particular, this does not itself derive the translated PA induction axiom, establish closed-formula environment independence, give a native iPRA theorem, or verify the machine.

Run `bash check-iso-successor-supplied.sh REPO NEW_OUTPUT`. The new source is rebuilt in a fresh output against pinned prebuilt inputs, including the repository-replayed existentially eliminated successor-property module. This is not a full transitive source rebuild. Success includes five axiom reports without `sorryAx`.
