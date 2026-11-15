# Uniform induction-step proof shift

`shift_inductionStepCode` proves the step constructor commutes with free-variable shift for arbitrary internally valid arity-two component codes. `shift_propertyOne` proves the nontrivial interchange between shift and the bound-variable substitution used for the predecessor occurrence. `stepTemplate_shift` combines these facts with shift-invariance of the three actual closed ordinal templates. The input p can be a nonstandard internally valid property code.

`shiftStepProofGraph` is one fixed parameter-free Σ₁ arithmetic formula. `shiftStepProofGraph_defined` proves that it computes `shiftStepProofCode` throughout each covered candidate-PRA + induced-IΣ₁ model. Given any internal Δ₁ source theory, valid internal p, and actual internal proof d of the ordinal induction step for p, `shiftStepProofDirect` constructs an internal proof of the step for shifted p; `shiftStepProofDirect_val` verifies that its proof code is exactly the graph output. The fixed template quotations are built compositionally rather than by expanding their Gödel numbers.

This implements the model-level counterpart of the standard proof's `inductionStepShift`. It does not supply the arbitrary-property ordinal induction sequent, a general PA proof compiler, or a native iPRA theorem.

Run `Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-step-shift.sh "$REPO" FRESH_OUTPUT` to compile both sources in one output against the repository-replayed base-shift and fixed-quotation objects and prebuilt transitive overlays listed in the checker. It hashes the sources and immediate objects and checks seven axiom reports for `sorryAx`. Passing output `/dev/shm/pa194-induction-step-shift-replay`; log `/tmp/pa194-induction-step-shift-replay.log`.
