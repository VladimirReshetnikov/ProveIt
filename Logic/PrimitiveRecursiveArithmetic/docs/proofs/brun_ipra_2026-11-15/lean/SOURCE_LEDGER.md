# Source and toolchain ledger

Inspected on 2026-11-15. Repository reads were performed through the GitHub
plugin. The snapshot was fixed before source inspection.

## Repository snapshot

- Repository: https://github.com/VladimirReshetnikov/ProveIt
- Commit: `8c135f6f2a9d041cde785a1a632c44ad98065b20`
- Commit time: 2026-11-15 20:31:36 UTC
- Root tree: `a01bc7dc82c8ce5e8af9b7848ec807fb9a85564c`
- Pinned Lean toolchain: `leanprover/lean4:v4.32.0`
- Pinned Mathlib: `leanprover-community/mathlib`, revision `v4.32.0`
- Root Lake configuration: `lakefile.toml` (not `lakefile.lean`)

## Foundational source files read

All following paths are relative to the repository root and were read at
the above commit, not merely inferred from file names.

1. `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/README.md`
   - Blob `8f810145b9ac8502748080a4ec4f15f2ad4c99bb`.
   - Native scalar-core presentation and formalization inventory.
   - Reports upstream build status and axiom dependencies.
   - https://github.com/VladimirReshetnikov/ProveIt/blob/8c135f6f2a9d041cde785a1a632c44ad98065b20/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/README.md

2. `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean`
   - Blob `3251631592070d9ed3687cc0bf7dbd5eb452e46f`.
   - Defines `PR`, `PTm`, `PRAAx`, and `PRA.qfInd`.
   - Full first-order intuitionistic logic, PR defining equations, successor
     axioms, and quantifier-free induction.
   - https://github.com/VladimirReshetnikov/ProveIt/blob/8c135f6f2a9d041cde785a1a632c44ad98065b20/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean

3. `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PRAToScalar.lean`
   - Blob `8a392980b452c25c1d7ce0de620829bc3bd494c9`.
   - Defines `FromPRA.code` and `FromPRA.interp`.
   - Contains explicit proofs of translations of every `PRAAx` constructor,
     including `FromPRA.ax_ind` through `Teq.qfInd`.
   - https://github.com/VladimirReshetnikov/ProveIt/blob/8c135f6f2a9d041cde785a1a632c44ad98065b20/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PRAToScalar.lean

4. `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/BiInterpretation.lean`
   - Blob `9c8124e2bf7bb68540e5e41f234e1a44bad865da`.
   - Defines `biInterp`; proves `teq_iff_pra`, `pra_iff_teq`,
     round trips and equiconsistency.
   - https://github.com/VladimirReshetnikov/ProveIt/blob/8c135f6f2a9d041cde785a1a632c44ad98065b20/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/BiInterpretation.lean

5. `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean`
   - Blob `ccfe499b9687ea0e176f832686d8e492fe15544b`.
   - Defines `NFm.toPRA`, `NFm.ofPRA`; proves `native_iff_pra`
     and `pra_iff_native`, round trips and equiconsistency.
   - https://github.com/VladimirReshetnikov/ProveIt/blob/8c135f6f2a9d041cde785a1a632c44ad98065b20/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean

The paper does not assume that an arbitrary finite true arithmetic statement
is provable in iPRA. It uses the source's exact induction discipline and
supplies the finite proof to be internalized.

## Draft inspected

`docs/drafts/prime_reciprocal_ipra_2026-11-15.zip`
(blob `9fda22afd9a58947bf79e1c044adf28b8da3251a`, 397,336 bytes)
was fetched through the GitHub file API in base64 encoding and unpacked.

Read:
- `prime_reciprocal_ipra.tex` (relevant bounded-factorization, finite
  harmonic, and iPRA-internalization sections);
- `lean/FORMALIZATION_PLAN.md`;
- `lean/PrimeReciprocalIPRA.lean`.

This draft contains a human proof of reciprocal-prime divergence and a Lean
scaffold with explicit `sorry` placeholders. It is not a completed Lean
number-theory dependency for the present work. The bounded factor-trace and
arithmetic-internalization methodology informed this package; the sieve
proof is developed independently.

Source:
https://github.com/VladimirReshetnikov/ProveIt/blob/8c135f6f2a9d041cde785a1a632c44ad98065b20/docs/drafts/prime_reciprocal_ipra_2026-11-15.zip

The inspected `docs/drafts` directory had no Brun-named archive. A GitHub
code search for "Brun sieve Selberg" returned no matches; this is not an
exhaustive claim that no related lemma exists anywhere in the repository.

## Verification status

- Foundation source declarations were inspected.
- The foundation was not rebuilt locally for this package.
- No Lean or Lake executable was found on PATH or in the usual shallow
  installation locations examined.
- The included Lean specification and candidate conditional assembly proofs
  are uncompiled source artifacts; no successful Lean build or kernel
  verification is claimed.
- The repository itself was not modified, and no commit or PR was created.

