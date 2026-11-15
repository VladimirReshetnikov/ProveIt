# Source successor property with the predecessor witness eliminated

`PA194IsoSuccessorProperty.lean` composes the contextual predecessor-matching theorem, the source successor application in its opened witness branch, and the existential witness eliminator. It proves P(c)(b) from explicit contextual proofs of Q(c)(p), successor(p,a), the guard `domain(b) ∧ orderIso(a,b)`, and the fixed universal matching theorem, plus explicit direct source ordinal-step and target-domain proofs in the shifted witness context. It checks the shift identity needed to return the result to the original context.

The arbitrary internal arity-one code c can be nonstandard. `isoSuccessorPropertyProof_val` gives the exact proof code and `isoSuccessorPropertyGraph_defined` provides one fixed Σ₁ graph in every candidate-PRA model with IΣ₁ arithmetic reduct. The supplied direct ordinal-step and target-domain proof codes remain explicit; their construction from the original source context and the PA translation is not established by this module.

This result is compatible with guarded identity packets. It does not yet give the translated PA induction axiom, establish closed-formula environment independence, prove an iPRA theorem, or verify the machine.

Run `bash check-iso-successor-property.sh REPO NEW_OUTPUT`. The module is rebuilt in a fresh output with pinned prebuilt dependencies including the repository-replayed source successor and Q-guard matching modules; it does not rebuild the full transitive source closure. Success contains three axiom audits excluding `sorryAx`.
