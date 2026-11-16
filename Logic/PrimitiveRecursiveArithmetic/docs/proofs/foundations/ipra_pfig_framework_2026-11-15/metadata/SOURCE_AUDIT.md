# Source audit

## Repository snapshot

- Repository: `VladimirReshetnikov/ProveIt`
- Audited tree: `Logic/PrimitiveRecursiveArithmetic`
- Snapshot used in the report: `34816faca8aa605999290b41d26210753b5c3b38`
- Audit date: 2026-11-15 (America/Los_Angeles)

## Inspected high-level sources

- `Logic/PrimitiveRecursiveArithmetic/README.md`
  - Describes the target iPRA presentation and checked `ConciseIPRA` backend.
  - Records 72 delivered proof packets and their repository verification caveat.
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/README.md`
  - Index of domain and foundation packets.
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/README.md`
  - Native scalar core, ordinary PR presentation, and bi-interpretation summary.

## Inspected object-language sources

- `ConciseIPRA/Lean/ConciseIPRA/Deduction.lean`
  - `Prf`, substitution, weakening, simultaneous cut, equality transport.
- `docs/proofs/foundations/ipra_coherent_methods_2026-11-15/lean/ObjectComposition.lean`
  - Exact term contracts, specialization, composition, and loop certificate example.
- `docs/proofs/foundations/ipra_local_global/lean/ObjectIteration.lean`
  - Source-complete `primitiveRecursionInvariant` and `primitiveRecursionAt` object derivations.
- `docs/proofs/algebra/ipra_stable_observables/lean/ObjectObservation.lean`
  - Source-complete stable-observer and finite-loop certificate combinators.
- `docs/proofs/foundations/ipra_local_global/lean/NegativeSyntax.lean`
  - Negative translation syntax and translated axioms; explicit remaining goals.
- `ConciseIPRA/Lean/ConciseIPRA/EqCompare.lean`
  - Comparator infrastructure in the equational layer.

## Inspected synthesis sources

- `docs/proofs/foundations/ipra_unified_finitary_framework_2026-11-15/README.md`
- `.../THEOREM_LEDGER.md`
- `.../metadata/difficulty_matrix.csv`

The PFIG report builds on these ideas but adds the fixed-graph-to-one-loop normalization, a three-mode elimination discipline (exact/search/stable), and a fully developed human proof of the retained negative-transfer theorem.

## Caution

This artifact did not clone or compile the repository. GitHub source content was inspected through the connected GitHub tool. Existing object theorems are therefore cited as inspected source, not independently reverified build results.
