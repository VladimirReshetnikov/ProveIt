# Source audit

## Pinned repository snapshot

- Repository: `VladimirReshetnikov/ProveIt`
- Branch inspected: `main`
- Commit: `9df5cbdf39e6220be823f611987bd584d37711fd`
- Commit time: 2026-11-16 05:24:07 UTC (2026-11-15 in America/Los_Angeles)

The package does not modify upstream files.

## Close-out head check

At package close-out, `main` had advanced to
`976e82c3b27401ac97038100d257680973e72dc6` (2026-11-16 05:38:44 UTC).
The head commit inspected changes only files under
`Computability/BusyBeaver/Research/PA/`. The current iPRA subtree README,
`ConciseIPRA/Lean/ConciseIPRA/PR.lean`, and
`ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean` retained the same
blob hashes as at the pinned snapshot. The archive therefore keeps the pinned
commit instead of silently changing its formalization target.

## Primary files inspected

- `Logic/PrimitiveRecursiveArithmetic/README.md`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/README.md`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/README.md`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Syntax.lean`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Deduction.lean`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/ipra_unified_finitary_framework_2026-11-15/README.md`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/ipra_unified_finitary_framework_2026-11-15/THEOREM_LEDGER.md`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/ipra_unified_finitary_framework_2026-11-15/metadata/difficulty_matrix.csv`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/ipra_unified_finitary_framework_2026-11-15/lean/TraceCompilerBlueprint.lean`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/ipra_cfp_contract_compiler_2026-11-15/README.md`

## Repository facts used by the report

1. The top-level iPRA README distinguishes the kernel-checked `ConciseIPRA`
   library from the delivered proof packets, which were filed without rerunning
   or compiling them.
2. At the pinned commit the packet index reports 72 proof packets across
   algebra, analysis, analytic number theory, combinatorics, Diophantine number
   theory, foundations, geometry, probability, and topology.
3. The exact upstream object-language API used here is:
   `PR`, `PTm`, `PRAAx`, `Prf`, `PRA.qfInd`, `NFm.ofPRA`, and
   `pra_iff_native`.
4. The unified-framework ledger at the pinned snapshot explicitly leaves implementation and
   kernel checking of a generic `Prf PRAAx` compiler open.
5. The repository's recurring unresolved producer obligations include general
   height bounds, rational covering representatives, ineffective analytic
   constants, unrestricted exact branch selectors, and conversion of mere
   metastability to a Cauchy modulus.

## Audit limitations

The GitHub snapshot was read through the connected GitHub API. The full
multi-gigabyte repository was not cloned into the artifact runtime, and Lean
was not installed there. Consequently:

- the new Lean files are source blueprints and were not compiled;
- upstream packet claims are treated as packet claims unless they belong to
  the kernel-checked `ConciseIPRA` files above;
- Python tests in this package are semantic regression evidence, not iPRA
  derivations.
