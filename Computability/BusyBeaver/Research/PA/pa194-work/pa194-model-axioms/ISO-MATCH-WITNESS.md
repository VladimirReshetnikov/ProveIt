# Contextual elimination of a predecessor witness

`PA194IsoMatchWitness.lean` expands the predecessor-match conclusion at arbitrary model-valued indices `(a,b,p)` as an existential over the explicit arity-four witness body `domain(y) ∧ (successor(y,b) ∧ orderIso(p,y))`. `isoMatchGoal_expanded` checks the exact typed substitution through the existential binder.

`isoMatchWitnessProof` eliminates that existential using an explicitly supplied witness branch under the shifted context; the branch proves the shifted goal in the presence of the negated opened witness body in the one-sided sequent. `isoMatchWitnessProof_val` identifies the proof code and `isoMatchWitnessGraph_defined` defines a fixed Σ₁ graph for it in every candidate-PRA model with an IΣ₁ arithmetic reduct.

The source theory, context, existential proof and witness-branch proof are explicit; the branch has not been built here. This result is compatible with guarded identity packets but does not establish the Q step, the PA induction translation, closed-formula environment independence, a native iPRA theorem, or machine correctness.

Run `bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-iso-match-witness.sh REPO NEW_OUTPUT`. The new source is rebuilt in a fresh output against pinned prebuilt dependencies; this is not a full transitive source rebuild. Success reports four axiom audits without `sorryAx`.
