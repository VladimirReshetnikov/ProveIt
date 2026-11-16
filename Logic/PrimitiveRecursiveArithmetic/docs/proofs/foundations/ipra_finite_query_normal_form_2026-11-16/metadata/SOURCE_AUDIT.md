# Source audit

## Repository snapshot

- Repository: `https://github.com/VladimirReshetnikov/ProveIt`
- Branch: `main`
- Snapshot used for the close-out audit:
  `31784f0710fa04ccd8ee863ce9bad91fb1d8cf88`
- Snapshot timestamp reported by GitHub: 2026-11-16 16:53:09 UTC
- Lean toolchain in the repository: `leanprover/lean4:v4.32.0`
- Mathlib revision in `lakefile.toml`: `v4.32.0`

The final snapshot commit adds six binary archives under
`Logic/PrimitiveRecursiveArithmetic/docs/incoming/`. They were not yet placed
under `docs/proofs` and their contents were not available through the UTF-8-only
repository connector. This package therefore makes no claim about their
internal proposals. The comparison and novelty audit concern the integrated,
inspectable source tree.

## Files inspected directly

### Backend syntax and proof theory

- `Logic/PrimitiveRecursiveArithmetic/README.md`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/README.md`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Deduction.lean`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean`
- `lean-toolchain`
- `lakefile.toml`

### Checked derivation library

- `Logic/PrimitiveRecursiveArithmetic/Derivations/README.md`
- `.../Core/Basic.lean`
- `.../Core/Definitions.lean`
- `.../Core/BoundedSums.lean`
- `.../Core/Pairing.lean`
- `.../Core/Search.lean`
- `.../Core/Division.lean`

### Existing cross-domain frameworks

- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/README.md`
- `.../foundations/ipra_certified_finitary_framework_2026-11-15/README.md`
- `.../foundations/ipra_finitary_interface_compiler_2026-11-15/README.md`
- `.../foundations/ipra_kernel_finite_use_framework_2026-11-15/README.md`
- `.../foundations/ipra_kernel_finite_use_framework_2026-11-15/THEOREM_LEDGER.md`
- `.../foundations/ipra_kernel_finite_use_framework_2026-11-15/metadata/difficulty_matrix.csv`
- `.../foundations/ipra_pfig_framework_2026-11-15/README.md`
- `.../foundations/ipra_proof_carrying_observation_graphs_2026-11-15/README.md`
- `.../foundations/ipra_embedding_framework_2026-11-15/metadata/difficulty_matrix.csv`
- `.../foundations/ipra_local_global/lean/ObjectIteration.lean`
- `.../algebra/ipra_stable_observables/lean/ObjectObservation.lean`

## Audit conclusion

The integrated tree already contains many variants of finite observations,
contract DAGs, proof graphs, backward demand, relational viability, and stable
observables. Repeating one of those graph architectures would add little. The
clearest common implementation gap, explicitly recorded by the existing
kernel-facing theorem ledger, is the object-iPRA arithmetic of bounded lists,
tables, resource vectors, finite relational selection, and the bridge from
those codes to the generic logical compilers.

FQNF targets that gap. Its distinguishing normal-form move is to encode the
entire finite certificate -- including complete relational paths and, when
useful, all node certificates of a fixed graph -- as one bounded natural
number, verify it by one fixed QF Boolean checker, and select the least accepted
code with the already checked bounded-search library. This does not replace
efficient domain algorithms; it gives them a common proof-theoretic fallback
and a sharply delimited Lean implementation target.
