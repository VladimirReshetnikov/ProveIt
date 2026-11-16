# Targeted source audit

## Baseline

- Repository: `VladimirReshetnikov/ProveIt`
- Branch: `main`
- Pinned commit: `c88269a745aedaca1235895c4d5e3e97056a1636`
- Audit date: 15 November 2026, America/Los_Angeles

This is a targeted review, not a blanket correctness audit of every packet.

## Arithmetic backend inspected

- `Logic/PrimitiveRecursiveArithmetic/README.md`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean`
  - Git blob reported by GitHub: `3251631592070d9ed3687cc0bf7dbd5eb452e46f`
  - Relevant declarations: `PR`, `PTm`, `PRAAx`, `PRA.qfInd`.
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean`
  - Git blob: `ccfe499b9687ea0e176f832686d8e492fe15544b`
  - Relevant declarations: `NFm.toPRA`, `NFm.ofPRA`, `native_iff_pra`, `pra_iff_native`.

## Foundational packets inspected

- `docs/proofs/foundations/ipra_framework/README.md`
- `docs/proofs/foundations/ipra_framework/lean/README.md`
- `docs/proofs/foundations/ipra_framework/lean/FiniteContracts.lean`
  - Git blob: `db479f615fda19a24d34b64ceab301fd030e0623`
- `docs/proofs/foundations/ipra_embedding_framework_2026-11-15/README.md`
- `docs/proofs/foundations/ipra_embedding_framework_2026-11-15/metadata/difficulty_matrix.csv`
- `docs/proofs/foundations/ipra_coherent_methods_2026-11-15/README.md`
- `docs/proofs/foundations/ipra_finite_observation/README.txt`
- `docs/proofs/foundations/ipra_evidence_framework/README.md`
- `docs/proofs/foundations/ipra_local_global/README.txt`
- `docs/proofs/foundations/ipra_uniform_certificates/README.md`

## Topology packets inspected

- `docs/proofs/topology/dimension_invariance_ipra/README.md`
- `docs/proofs/topology/jordan_ipra_constructive_2026-11-15/README.md`

## Principal audit conclusions

1. The actual formal endpoint is `Γ ⊢[PRAAx] φ`; ambient Lean truth is not enough.
2. Existing frameworks already provide finite contracts, fixed evaluators,
   Boolean invariants, object examples, coherent finite observations, and
   relational-output ideas.
3. The topology packets contain substantial complete human arguments but leave
   theorem-specific Lean/object derivations unfinished.
4. The common remaining topology gap is a reusable, choice-stable calculus for
   refinement maps and invariants. The present package addresses it with strong
   simplicial carriers and an explicit prism homotopy.
5. No universal unclocked evaluator for arbitrary PR program codes is assumed.

## External mathematical references

The report uses primary or standard sources for finite spaces, represented
spaces, constructive/formal topology, carrier methods, constructive Jordan
separation, discrete Jordan proofs, and reverse-mathematical limits. Full
bibliographic data and DOI/arXiv identifiers are in the report.
