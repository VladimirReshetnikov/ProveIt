# The Q guard from an opened predecessor witness

`PA194IsoWitnessComponents.lean` expands the opened predecessor witness into its domain, successor, and isomorphism components. It proves the exact eigenvariable identity `domain(0) ∧ orderIso(p+1,0) = isoGuardTemplate[0,p+1]`: opening the existential introduces a fresh free variable at index zero and shifts the existing free index p by one. This preserves the distinct-variable discipline of the guarded compiler.

`isoWitnessGuardProof` constructs a proof of that Q guard from an explicit proof of the opened witness under an arbitrary common source context. `isoWitnessGuardProof_val` identifies the exact proof code; `isoWitnessGuardGraph_defined` gives a fixed Σ₁ graph defining it in every candidate-PRA model with an IΣ₁ arithmetic reduct. The proof projects the domain and isomorphism components and combines them.

The opened witness proof is an explicit input. This does not yet build the full existential witness branch, the Q induction step or the actual PA translation/substitution bridge; native iPRA internalization and machine correctness are also open. Closed-formula environment independence is separately established in [the arithmetic packet bridge](../pa194-model-logic/CLOSED-SENTENCE.md).

Run `bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-iso-witness-components.sh REPO NEW_OUTPUT`. This rebuilds the new source in a fresh output against pinned prebuilt dependencies, including the repository-replayed predecessor-witness module. It is not a full transitive source rebuild. A successful output contains five axiom audits without `sorryAx`.
