# Contextual Q zero adapter

`PA194IsoGuardZero.lean` constructs a proof of Q(c)(a) in an arbitrary source context from explicit contextual proofs of zero(a), the fixed universal zero-isomorphism theorem, and the direct source ordinal-base formula for c. Here Q(c)(x) universally requires P(c) at every domain element isomorphic to x; c is any internally valid arity-one code, including a nonstandard code.

The construction shifts c, the context and the zero argument under a fresh eigenvariable, opens Q, invokes the pointwise zero-property adapter, and closes Q. `isoGuardZeroProof_val` identifies its proof code and `isoGuardZeroGraph_defined` gives one fixed Σ₁ graph in every candidate-PRA model with IΣ₁ arithmetic reduct.

The direct source base proof and universal zero-isomorphism theorem remain explicit inputs. This is not yet a derivation of the translated PA induction axiom, a native iPRA theorem, or machine correctness.

Run `bash check-iso-guard-zero.sh REPO NEW_OUTPUT`. This recompiles the new source into a fresh output against pinned prebuilt inputs, including the exact repository-replayed pointwise zero and Q successor modules; the full transitive source closure is not rebuilt. Success includes three axiom reports without `sorryAx`.
