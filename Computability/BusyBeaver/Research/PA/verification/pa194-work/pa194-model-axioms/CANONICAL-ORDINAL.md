# Deterministic full-source ordinal proof-code constructors

The first four modules define a fixed Δ₁ proof predicate for each fixed source sentence, a fixed Δ₁ predicate for a paired tuple of eight auxiliary proofs, a fixed Σ₁ graph for the least valid tuple, and a fixed Σ₁ graph for the resulting closed ordinal-induction proof code. In every PRA model whose arithmetic reduct models IΣ₁, the tuple exists and is unique. Its value can vary between models, but its defining formula is fixed.

For every internally valid arity-one source-property code p, including nonstandard codes, `canonicalClosedOrdinalProof_val` identifies the exact code of a proof of `closedOrdinalInductionCode p` in the full source theory. The fifth module uses the model-length reopening iterator to supply an analogous fixed Σ₁ graph and exact proof code for the open `ordinalInductionCode p`. Both graphs take only p as input and have no external seed-proof inputs.

These are Lean model-level theorems. The proof interpretation of PA, native iPRA formalization and machine equivalence remain separate obligations.

Run `bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-canonical-ordinal.sh "$PWD" /dev/shm/pa194-canonical-ordinal-repo-NEW` from the repository root. The checker compiles all five sources in one fresh output using hash-pinned prebuilt dependencies, rejects `sorryAx`, and checks axiom counts. The successful output is `/dev/shm/pa194-canonical-ordinal-replay`.
