# Uniform closed ordinal-induction proof code

`closedSeededOrdinalCode` composes the seeded full-source ordinal-induction code with the model-length closure iterator. For every internally valid property code p, including nonstandard codes, `closedSeededOrdinalProof` proves `closedOrdinalInductionCode p`; its exact computed value and a fixed Σ₁ graph are checked. The eight codes of fixed property-independent source-theorem proofs remain explicit inputs. The assumptions are a PRA model with IΣ₁ arithmetic reduct. This is a Lean model-level theorem, not a PA interpretation or native iPRA result.

Run `bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-ordinal-closed-seeded-code.sh "$PWD" /dev/shm/pa194-ordinal-closed-seeded-code-repo`. It compiles this source against hash-pinned prebuilt dependencies and rejects `sorryAx`; successful output is `/dev/shm/pa194-ordinal-closed-seeded-code-replay`.
