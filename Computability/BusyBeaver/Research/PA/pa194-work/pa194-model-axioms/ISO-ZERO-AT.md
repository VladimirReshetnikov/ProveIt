# Pointwise Q zero-property application

`PA194IsoZeroAt.lean` constructs P(c)(b) in a common source context from proofs of zero(a), the guard `domain(b) ∧ orderIso(a,b)`, the fixed universal zero-isomorphism theorem, and the direct ordinal-base formula for c. It specializes the zero-isomorphism theorem, extracts the guard's domain and isomorphism components, and applies the direct ordinal-base proof at b. The source theory and all input proof codes are explicit, and c is any internally valid arity-one code, including nonstandard codes.

`isoZeroAtProof_val` checks the exact proof code, and `isoZeroAtGraph_defined` supplies one fixed Σ₁ graph in every candidate-PRA model with IΣ₁ arithmetic reduct. The direct source base proof remains an input; this is not a proof of the translated PA induction axiom, closed-formula environment independence, a native iPRA theorem, or machine correctness.

Run `bash check-iso-zero-at.sh REPO NEW_OUTPUT`. It rebuilds the new source in a fresh output against pinned prebuilt inputs, including the repository-replayed zero-isomorphism theorem and Q syntax. This is not a full transitive source rebuild. Success includes seven axiom reports with no `sorryAx`.
