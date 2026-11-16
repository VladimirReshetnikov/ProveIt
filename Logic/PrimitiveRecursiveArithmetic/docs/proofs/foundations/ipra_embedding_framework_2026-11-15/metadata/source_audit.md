# Source audit

## Snapshot

- Repository: `VladimirReshetnikov/ProveIt`
- Main commit inspected: `7d492fbfc5fee3b2b9dec0b2623b0b82effe05f2`
- Access method: read-only GitHub connector.
- A local network clone was unavailable in the artifact runtime.

## Foundation

- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/README.md`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Native.lean`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/BiInterpretation.lean`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativePublic.lean`

These files supplied the actual interfaces used in the Lean plan: `PR`, `PTm`,
`PRAAx`, `PRA.qfInd`, `NFm`, `NPrf`, `pra_iff_native`, and the guarded public
calculus.

## Packet index and representative difficulty reports

- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/README.md`
- `.../geometry/euler_rodrigues_ipra/README.md`
- `.../geometry/euler_rodrigues_ipra/formalization_and_audit.tex`
- `.../diophantine-number-theory/dirichlet_kronecker_ipra/README.txt`
- `.../analytic-number-theory/zeta_ipra_proof_package/paper/sections/01_foundations.tex`
- `.../analytic-number-theory/prime_distribution_ipra/paper/sections/01_scope.tex`
- `.../diophantine-number-theory/faltings_ipra/README.md`
- `.../diophantine-number-theory/siegel_ipra/paper/01_scope.tex`
- `.../diophantine-number-theory/mordell_weil_ipra/README.txt`
- `.../probability/central_limit_ipra_2026-11-15/paper/central_limit_ipra.tex`

The packet index explicitly says placement did not rerun or verify the
archives. The individual reports were used for their own stated scope and
obstacles; this artifact does not infer correctness of uncompiled files.

## Main extracted themes

1. Fix precision before quantifier-free induction.
2. Use fixed PR evaluator schemas, not a universal total PR evaluator.
3. Distinguish exact/projective/approximate outputs and require gaps for exact
   branch selection.
4. Treat height bounds, covering representatives, and analytic constants as
   explicit producer outputs or certificates.
5. Do not confuse ambient Lean theorems with embedded `Prf PRAAx` derivations.
