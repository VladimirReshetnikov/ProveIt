# Full-source greatest-image proofs

The fixed five-free-variable `greatestImageStatement` says that if g is an order-bijection from a to b, x is greatest in a, and g relates x to y, then y is greatest in b. `greatestImageStatementProof` is a Foundation derivation from four explicit equality principles. `greatestImageOpenProof` discharges those premises with existing full-source equality and congruence proofs, yielding a proof of that fixed open formula in every PRA model with IΣ₁ arithmetic reduct.

`greatestImageClosedCode` closes all free variables using the internally computed free-variable bound. `greatestImageClosed_sentence` shows it is a sentence and shift-fixed, and `greatestImageClosedProof` supplies a full-source proof. `greatestImageClosedGraph_defined` is a fixed Σ₁ graph for the **sentence code**. It is not a graph for the proof code; arbitrary model-index specialization and a uniform proof-code supplier are not established here.

This is an ingredient toward transport of successors under order-isomorphism. A restricted order-bijection, the actual successor transport, translated PA induction, native iPRA formalization and machine equivalence remain separate obligations.

Run `bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-order-iso-greatest-source.sh "$PWD" /dev/shm/pa194-order-iso-greatest-source-repo-NEW` from the repository root. It source-compiles the three add-on modules in a fresh output against hash-pinned prebuilt dependencies, including the repository-replayed greatest-image derivation, unified PairGraph syntax and source equality suppliers. The successful output is `/dev/shm/pa194-order-iso-greatest-source-replay`.
