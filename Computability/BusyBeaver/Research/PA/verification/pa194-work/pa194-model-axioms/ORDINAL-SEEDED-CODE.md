# Uniform ordinal induction with fixed-theorem seeds

`seededOrdinalCode p ...` composes the full-source separation-root code (applied to the negated property) with the previously checked ordinal-induction constructor. `seededOrdinalCodeGraph_defined` gives a fixed Σ₁ graph, and `seededOrdinalProof_val` proves the computed code gives the actual proof for all internally valid property codes, including nonstandard ones. The remaining eight inputs are proofs of fixed, property-independent source theorems. The result is a model-level theorem for PRA models with IΣ₁ reduct; it is not a native iPRA derivation or a PA interpretation.

Run `bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-ordinal-seeded-code.sh "$PWD" /dev/shm/pa194-ordinal-seeded-code-repo` from the repository root. The checker compiles this source against hash-pinned prebuilt dependencies and rejects `sorryAx`. Successful output: `/dev/shm/pa194-ordinal-seeded-code-replay`.
