# Shifting the isomorphism-guarded property

`PA194IsoGuardShift.lean` proves that shifting `Q(c)` shifts the internal property code c as well as every free source variable, and that shifting an application `Q(c)(a)` yields `Q(shift c)(a+1)`. The code c can be any internally valid arity-one formula, including nonstandard codes. The theorem uses the shift-invariance of the fixed closed guard and does not identify any free indices.

`isoGuardShiftProof` constructs a proof of the shifted application in the shifted one-sided context from an explicit proof of the original application. `isoGuardShiftProof_val` identifies its code and `isoGuardShiftGraph_defined` gives a fixed Σ₁ definition of the constructor in every candidate-PRA model with IΣ₁ arithmetic reduct.

The source theory, context and initial proof remain explicit. This adapter alone does not discharge the witness branch or prove the translated PA induction axiom, closed-formula environment independence, an iPRA theorem, or machine correctness.

Run `bash check-iso-guard-shift.sh REPO NEW_OUTPUT`. The new source is rebuilt in a fresh output against pinned prebuilt inputs, including the repository-replayed Q application; the transitive dependencies are not rebuilt. A successful output includes five axiom reports without `sorryAx`.
