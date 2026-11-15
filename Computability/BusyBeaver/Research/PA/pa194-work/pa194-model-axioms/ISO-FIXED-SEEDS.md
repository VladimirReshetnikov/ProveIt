# Full-source Q adapters with fixed-theorem proof seeds

`PA194IsoFixedSeeds.lean` defines the least full-source proof code of any fixed standard sentence that has a supplied full-source proof. It proves the least code exists in every candidate-PRA model with an IΣ₁ arithmetic reduct and that one fixed Σ₁ graph defines it. The chosen code can differ between models; the graph is parameterized by the fixed standard sentence, not by an arbitrary internal formula code.

For the two fixed sentences needed here, existence is supplied by the already checked zero-isomorphism proof and the full-source universal predecessor-matching proof. `fullZeroProof` and `fullSuccessorProof` then give the contextual Q zero and successor adapters without requiring either fixed-theorem proof code as an input. Their exact proof codes are given by `fullZeroProof_val` and `fullSuccessorProof_val`, and each has one fixed Σ₁ graph. Arbitrary internal property codes c may be nonstandard.

The original direct ordinal-base or ordinal-step proof and the relevant zero, successor, or Q premises remain explicit inputs. The construction is model-level and does not yet prove the translated PA induction axiom, native iPRA internalization, or machine correctness.

Run `bash check-iso-fixed-seeds.sh REPO NEW_OUTPUT`. It recompiles the new source into a fresh output against pinned prebuilt dependencies, including the exact repository Q adapters and fixed-theorem modules. This is not a full transitive source rebuild. Success includes ten axiom reports excluding `sorryAx`.
