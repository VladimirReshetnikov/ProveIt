# Q property at the predecessor witness

`PA194IsoWitnessBranch.lean` constructs the predecessor-property portion of the existential witness branch. Given only a proof of Q(c) at the original predecessor index p under Γ, it shifts that proof and the internal property code c, weakens into the shifted context containing the negated opened witness, derives the opened witness by identity, and obtains the shifted property at the fresh witness index 0. This preserves distinct free variables and is compatible with the guarded identity-packet discipline.

`isoWitnessBranchProof_val` identifies the exact code; `isoWitnessBranchGraph_defined` gives a single fixed Σ₁ graph for all candidate-PRA models with IΣ₁ arithmetic reduct and arbitrary internally valid c, including nonstandard codes. The proof of Q(c)(p) and the source context are explicit inputs.

This is only the predecessor-property portion of the witness branch. It does not apply the source successor step to reach the target property, prove the actual PA induction translation or closed-formula environment independence, internalize a theorem in iPRA, or verify the machine.

Run `bash check-iso-witness-branch.sh REPO NEW_OUTPUT`. The module is rebuilt in a fresh output against pinned prebuilt inputs, including the repository-replayed witness-property and the repository-replayed Q shift modules. This is not a transitive source rebuild. A successful run reports three axiom audits without `sorryAx`.
