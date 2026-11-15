# Internal empty-set proof and two-premise reduction

`emptyFromFalseSeparation` is a standard typed source derivation of `emptyFormula` from the single instance `separationFormula ⊥`. It uses the existing parameter-preserving separation trace and first-order proof rules: an arbitrary set supplies a separation witness, and the false predicate proves that witness has no members.

`emptyProof` quotes this standard derivation into each covered model, discharges its separation assumption using the classifier-defined source theory, and constructs an actual internal proof of `⌜emptyFormula⌝` in `adjunctiveFullSepTheory`. Combining this with the previous three-premise reduction, `standardOrdinalProofOfTwo` constructs the internal ordinal-induction proof for every **standard typed** property p, conditional on internal proofs of the two remaining fixed source formulas: `adjunctionFormula` and `congruenceFormula`.

The section assumes a nonempty candidate-PRA model with IΣ₁ on its induced ordered-ring arithmetic. The result does not supply the two remaining hypotheses, cover arbitrary nonstandard property codes, construct a uniform internal proof-code transformer, or establish a native iPRA theorem.

`Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-empty-source-proof.sh "$REPO" FRESH_OUTPUT` recompiles both new modules into one output, using the repository-replayed three-premise reduction and the prebuilt Foundation/source overlays listed in the checker. It hashes both sources and immediate dependency objects and checks four axiom reports. Passing output `/dev/shm/pa194-empty-source-proof-replay`; log `/tmp/pa194-empty-source-proof-replay.log`. Transitive dependencies remain prebuilt.
