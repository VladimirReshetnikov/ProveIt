# Demand-Driven Relational Certificates for Mathematics in iPRA

Prepared for Vladimir Reshetnikov, 15 November 2026.

## Start here

- `ipra_finite_use_framework.pdf` — main human-readable report.
- `ipra_finite_use_framework.tex` and `sections/` — editable LaTeX source.
- `metadata/THEOREM_LEDGER.md` — claim-by-claim status.
- `metadata/CURRENT_REPOSITORY_CHECK.md` — post-snapshot audit against current main.
- `lean/FORMALIZATION_PLAN.md` — dependency-ordered path to checked Lean.
- `code/finite_use_kernel.py` — exact finite reference implementation.

## Main contribution

The report extends the existing ProveIt finite-observation, relational-evidence,
and Certified Finitary Presentation frameworks with a **finite-use relational
composition theorem**.

A producer may return a finite relation of locally valid answers rather than a
discontinuously chosen exact object. A bounded adaptive consumer is compiled
with that relation by a primitive-recursive backward-viability computation.
If the initial state is viable, a least-successful transcript is produced and
verified. Internal choices can be erased when the final observation is:

1. exactly invariant over all successful transcripts; or
2. quantitatively stable within a certified diameter.

This supports approximate roots, root clusters, projective directions, robust
charts, finite covers, and local algebraic choices without asserting an
unavailable global selector or infinite coherent branch.

## Developed results

The report gives detailed human proofs of:

- bounded Booleanization and least bounded search;
- deterministic finite-trace reflection;
- adaptive finite query tables for represented inputs;
- finite-use relational viability and composition;
- certificate reflection for relational interaction graphs;
- exact branch-invariant and approximate diameter-stable elimination;
- regular-name arithmetic and apartness-guarded reciprocal;
- precision-transformer and finite error-DAG composition;
- ranked metastability, with an explicit no-rate warning;
- root-cluster and quotient-level algebraic interfaces;
- finite-net transfer, approximate witness search, and nested names;
- height-bound / complete-list equivalence.

The report does **not** claim a general exact Puiseux selector for arbitrary
Cauchy coefficients, a general convergence-rate extraction from metastability,
or general Faltings, Siegel, Mordell–Weil, Chebotarev, or prime-distribution
producer theorems.

## Executable companion

The Python companion uses only the standard library and exact arithmetic:

```bash
cd code
python3 -m unittest -v test_finite_use_kernel.py
python3 finite_use_kernel.py
```

The delivered run passes 8 tests. The checks cover viability, transcript
replay, relational square-root chains, error-DAG propagation, metastability,
and bounded point enumeration. These are semantic finite tests, not iPRA proof
objects.

## Lean status

- `lean/FiniteUseSemantic.lean` gives host-level definitions and explicit goal
  propositions.
- `lean/ObjectTraceReflection.lean` targets the actual `ConciseIPRA` API and
  supplies a concrete generic `PRA.qfInd` wrapper once normalized base, step,
  and finish derivations are provided.
- The artifact environment did not contain Lean or a local ProveIt dependency
  closure, so neither file is claimed compiler-checked.
- No native export is claimed before a compiled `Prf PRAAx` endpoint exists.

## Rebuild

With TeX Live and Python 3:

```bash
bash build.sh
```

The script runs unit tests, executes the demo, compiles the PDF, and refreshes
SHA-256 hashes.

## Repository baselines

Primary technical audit, read-only:

- repository: `VladimirReshetnikov/ProveIt`
- directory: `Logic/PrimitiveRecursiveArithmetic`
- main commit: `0edaf721b175de6aa219755df18b1588be803a16`

Post-snapshot integration check, read-only:

- current main checked at: `bce5113f44d613f5625c274128ee761f35486fc5`
- the `ConciseIPRA` interfaces used here remain current;
- this packet has been filed under `docs/proofs/foundations/`;
- `algebra/ipra_stable_observables` now supplies five reported compiled
  object-level observation/loop combinators that can be reused in the Lean path.

The repository still states that delivered proof packets were not rerun or
verified. This archive likewise does not claim an independent Lean build. The
full audit is in `metadata/SOURCE_AUDIT.md`,
`metadata/CURRENT_REPOSITORY_CHECK.md`, and Appendix B of the report.
