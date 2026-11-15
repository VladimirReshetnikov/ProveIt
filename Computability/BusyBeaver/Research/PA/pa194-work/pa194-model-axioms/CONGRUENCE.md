# Internal source congruence proof and one-premise reduction

`relExt_syntax` identifies the actual Foundation membership equality axiom with its fully explicit typed source formula. `congruenceFromRelExt` specializes that axiom at the four appropriate variables and uses first-order logic to derive the exact `congruenceFormula` required by the existing ordinal proof.

`congruenceProof` quotes this derivation into each covered model and supplies its single axiom from the classifier-defined adjunctive/full-separation union. Combining it with the previous two-premise result gives `standardOrdinalProofOfOne`: for any **standard typed** property p it constructs an internal proof of the exact quoted ordinal-induction statement, conditional only on an internal proof of `adjunctionFormula` (exact adjunction).

The covered models are nonempty candidate-PRA models with IΣ₁ on induced ordered-ring arithmetic. Exact adjunction remains an explicit hypothesis. The result does not supply ordinal induction for nonstandard p, an arbitrary-property proof-code transformer, or an iPRA theorem.

Run `Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-congruence.sh "$REPO" FRESH_OUTPUT` to compile both new sources into one output against the repository-replayed empty and equality suppliers and prebuilt transitive dependencies listed in the checker. Immediate source and object hashes are checked; four axiom reports exclude `sorryAx`. Passing output `/dev/shm/pa194-congruence-source-proof-replay`; log `/tmp/pa194-congruence-source-proof-replay.log`.
