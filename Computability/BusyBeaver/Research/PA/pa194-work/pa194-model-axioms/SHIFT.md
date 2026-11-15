# Shifting internal separation proofs

For every model-internal valid arity-one property p (including nonstandard codes), `shift_sepRoot` proves `shift SourceL (sepRoot p) = sepRoot (shift SourceL p)`, and `shift_neg_sepRoot` gives the corresponding identity for separation of the negated property. The proof checks the source constructor and bound-variable shifts directly.

For any internal Δ₁ source theory, `shiftSeparationProof` and `shiftNegSeparationProof` transform actual Foundation internal proof structures along these identities, implementing the model-level analogue of the standard ordinal proof's `separationShift` helper. They require the respective input proof and well-formed property code; they do not prove the ordinal-induction sequent, establish a uniform definable graph for the proof transform, or establish an iPRA theorem.

The model assumptions are nonempty candidate PRA plus IΣ₁ in the induced ordered-ring reduct. Run `Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-shift.sh "$REPO" FRESH_OUTPUT` to recompile this source against the repository-replayed general-separation object and prebuilt transitive overlays. The checker verifies source and immediate object hashes and four axiom reports. Passing output `/dev/shm/pa194-internal-separation-shift-replay`; log `/tmp/pa194-internal-separation-shift-replay.log`.
