# Internal source proof of intersection

The standard ordinal-induction derivation `inductionDerivation` in `PA194FoundationOrdinalInductionNumeric.lean` assumes `intersectionFormula` alongside the finite equality/weak-adjunction axioms and separation for the negated property. This handoff supplies that fixed intersection premise in the actual classifier-defined union theory.

* `intersection_typed_separation` proves exact syntactic equality between the universal closure of the separation instance for `intersectionProperty (.fvar 0)` and the universal closure of `Ordinal.intersectionFormula`. This is not merely semantic or alpha-equivalence.
* `typed_separation_axiom_member` identifies every standard typed parameterized separation closure as an axiom of the model-internal union class.
* `intersection_axiom_member` combines these results and the no-free-variable property of `intersectionFormula` to show that its internal quotation is itself an axiom in `adjunctiveFullSepTheory.Δ₁Class`.
* `intersection_provable` uses the internal axiom rule to obtain an actual Foundation internal proof of the quoted intersection formula. Its generic helper avoids evaluating the enormous fixed Gödel numeral.

The latter theorems assume a nonempty candidate-PRA model and IΣ₁ for its induced ordered-ring arithmetic. They supply this one fixed premise in every such model, including nonstandard models. They do not prove the remaining parametric ordinal-induction derivation, define its proof-code graph, interpret arbitrary internal PA proofs, or establish a native iPRA consistency equivalence.

Run `Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-intersection.sh "$REPO" FRESH_OUTPUT` for the staged replay of the three sources into one output. The checker hashes those sources and immediate union and typed-schema oleans; its transitive dependencies are prebuilt as listed in the script. The passing output is `/dev/shm/pa194-intersection-proof-replay`, and log `/tmp/pa194-intersection-proof-replay.log`. All four printed axiom reports exclude `sorryAx`.
