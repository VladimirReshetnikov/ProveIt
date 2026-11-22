# From finite observations to continuous structures

Research package prepared for Vladimir Reshetnikov, 20 November 2026.

The full 43-page paper is `paper/report.pdf`; its editable LaTeX source is
`paper/report.tex` with the files in `paper/sections/`.

## What this package contributes

The framework develops explicit numerical presentations for continuous
objects, rather than adding real or function sorts to first-order iPRA.
Its principal results are:

1. A quantitative completion/extension interface that identifies the value
   of a function at a coherently constructed limit.
2. Weighted gluing with explicit sample error, coverage, support, and
   positive-denominator bounds.
3. Coherent exact-solution recovery from PR approximate witnesses and a
   PR residual-diameter modulus, including the real cube root at zero.
4. PR finite nets of **actual** bounded Lipschitz functions, built from
   clipped finite McShane envelopes; no table-feasibility oracle is needed.
5. Finite continuous-formula transfer under total approximate correspondences,
   with no quantifier-depth error loss for min, max, complement, inf, and sup.
6. Constructive continuous semantics and approximate extrema on supplied
   compact presentations, including function sorts with named sup distances.
7. A quantitative complex power-series interface and holomorphic descent
   under exact all-precision overlap compatibility.
8. An exact variational example: the largest integral of a 1-Lipschitz
   function with zero endpoints is 1/4. The tent function attains it, and
   its residual controls uniform distance to the optimizer.

## Verification status

The standalone `lean/` project **was compiled successfully with Lean 4.32.0**.
It has five modules, 41 named proved theorems, and no external package
dependencies. The single-sort core formula-transfer theorem is checked,
including arity-correct environments and arbitrary finite quantifier alternation.
The many-sorted theorem is proved in the paper; its Lean generalization,
needed directly for formulas mixing function and point sorts, remains outlined.
Its audited axioms are `propext` and `Quot.sound`, with no `Classical.choice`,
`sorryAx`, or custom correctness axioms.

**These are Lean semantic theorems, not completed new `Prf PRAAx` derivations.**
The new continuous results have detailed human proofs, finite arithmetic
invariants, and explicit formalization plans. The remaining deep embedding
work is recorded in `lean/ObjectTheoryPlan.lean.txt` and `blueprints/`.
The latter directory is not part of the checked Lake build. Definitions
named `...Goal` state targets and do not assert proofs.

The Python programs use exact rational arithmetic. Their recorded examples
and 13,710 continuous-layer checks are implementation validation, not
universal proofs. The paper was compiled and visually checked separately.

## Repository baseline and reuse

The audit uses ProveIt commit
`5f3be02388442f16487d2dc5c2529961dd783d2b`.
The inspected source is substantially more developed than the directory's
overview. This package explicitly credits its existing finite-net,
coherent-minimizer, setoid, gluing, bounded-induction, and obstruction work.
It does not claim those generic ideas were absent.

`metadata/source_manifest.json` records the immutable paths and hashes.
The existing ProveIt modules were inspected, **not rebuilt** in this session.
No repository branch or remote file was changed.

## Reproduce

```bash
# Python 3, standard library only
python3 code/run_examples.py
python3 code/validate_continuous.py

# Lean 4.32.0 and Lake
cd lean
lake build
lake env lean Audit.lean
cd ..

# TeX Live / latexmk
./build_pdf.sh
```

`check.sh` runs both Python programs and the Lean checks. The Lean toolchain
is pinned by `lean/lean-toolchain`; downloaded toolchain binaries and build
caches are deliberately excluded from the archive.

## Files

| Directory | Contents |
| --- | --- |
| `paper/` | Full PDF, main LaTeX file, and all section sources. |
| `lean/` | Compiled standalone finite semantic kernel and exact object-theory plan. |
| `blueprints/` | Uncompiled analytic/function-space definitions and theorem targets. |
| `code/` | Exact-rational reference algorithms and executable examples. |
| `metadata/` | Source manifest, theorem-status ledger, and source audits. |
| `validation/` | Build/axiom reports, arithmetic results, and mathematical review records. |

`SHA256SUMS` records the checksum of every other file in the archive.

The framework does not decide exact real equality, choose arbitrary infinite
branches, extract moduli from qualitative continuity, construct models of
arbitrary consistent theories, or interpret unrestricted analysis in iPRA.
Its useful strength comes from proving exactly which finite data suffice
for each continuous construction.
