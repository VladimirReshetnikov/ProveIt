# Uniform contextual proof shift

`contextShiftGraph` is a single parameter-free Σ₁ arithmetic formula for the explicit proof-code function `contextShiftCode r g d`. Its inputs are the code r of a formula, code g of a one-sided sequent context, and an input derivation code d. `contextShiftGraph_defined` establishes the graph throughout each nonempty candidate-PRA model with induced arithmetic IΣ₁.

For any internal Δ₁ source theory, well-formed internal formula r, internal source sequent Γ, and an actual derivation d of r under Γ, `contextShiftProof` constructs an actual derivation of shifted r under shifted Γ. `contextShiftProof_val` proves its code is definitionally the output of the fixed graph. The input formula, context, and derivation code may be nonstandard. This generic constructor can be combined with the separately checked source-code identities for separation and ordinal base/step shifts.

This is one internal proof rule, not the main ordinal-induction sequent, a complete PA proof-code compiler, or a native iPRA result.

Run `Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-context-shift.sh "$REPO" FRESH_OUTPUT` to recompile against the repository-replayed internal separation-shift object and its prebuilt transitive overlays listed in the checker. Source and immediate object hashes and three axiom reports are checked. Passing output `/dev/shm/pa194-context-shift-code-replay`; log `/tmp/pa194-context-shift-code-replay.log`.
