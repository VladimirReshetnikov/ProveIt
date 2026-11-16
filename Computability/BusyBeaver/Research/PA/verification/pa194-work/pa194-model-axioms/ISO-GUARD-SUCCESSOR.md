# Contextual successor adapter for the isomorphism guard

`PA194IsoGuardOpen.lean` constructs a proof of Q(c)(a) in an arbitrary source context from explicit contextual proofs of Q(c)(p), successor(p,a), the fixed universal predecessor-matching theorem, and the direct ordinal-step formula for c. Here `Q(c)(x)` universally requires P(c) at every domain element isomorphic to x. The internally valid arity-one code c may be nonstandard.

The construction opens Q with a fresh variable at index zero, shifts c and the existing context and indices, proves the shifted successor template ignores its unused middle index, derives the opened property from the supplied predecessor proof, and closes Q again. `isoGuardSuccessorProof_val` identifies its proof code, and `isoGuardSuccessorGraph_defined` gives one fixed Σ₁ graph in every candidate-PRA model with IΣ₁ arithmetic reduct.

The direct source ordinal-step proof, predecessor-matching theorem, and Q/predecessor premises remain explicit inputs. This is a contextual successor adapter, not yet a derivation of the actual translated PA induction axiom, closed-formula environment independence, an iPRA theorem, or machine correctness.

Run `bash check-iso-guard-successor.sh REPO NEW_OUTPUT`. This rebuilds the new source in a fresh output against pinned prebuilt inputs, including the exact repository-replayed original-context source successor and Q-shift modules. It does not rebuild the full transitive source closure. Success includes five axiom audits with no `sorryAx`.
