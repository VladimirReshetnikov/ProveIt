# Internal source suppliers for ordinal induction

`ordinal_source_suppliers` proves that, in every covered model and for every internally valid arity-one source code p, `adjunctiveFullSepTheory` has internal proofs of both the fixed `Ordinal.intersectionFormula` and `sepRoot (neg SourceL p)`. The latter is the parameterized separation premise for the negated property used by the existing standard ordinal induction derivation. The quantified p may be nonstandard.

`typed_negated_property_separation_provable` independently identifies the encoded second conclusion, for any standard typed property p, with `⌜separationFormula (∼p)⌝`, exactly the premise used in `PA194FoundationOrdinalInductionNumeric.lean`. This is an exact quotation result, including arbitrary free parameters.

These results assume a nonempty candidate-PRA model with IΣ₁ for its induced ordered-ring arithmetic. They establish existence of internal source proofs of these two premises. They do not supply the remaining uniform internal ordinal-induction derivation, define a parameter-free proof-code transformer, or prove a native iPRA consistency equivalence.

`Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-ordinal-suppliers.sh "$REPO" FRESH_OUTPUT` checks this source against the repository-replayed intersection object `/dev/shm/pa194-intersection-proof-repo`, the repository-replayed full-separation supplier `/dev/shm/pa194-full-sep-open-repo`, and their prebuilt transitive dependencies listed in the script. It checks source and immediate object hashes and three axiom reports. Passing output: `/dev/shm/pa194-ordinal-suppliers-replay-v2`; log `/tmp/pa194-ordinal-suppliers-replay-v2.log`.
