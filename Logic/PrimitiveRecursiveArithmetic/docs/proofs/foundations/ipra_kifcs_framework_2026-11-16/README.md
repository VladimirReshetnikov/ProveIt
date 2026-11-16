# KIFC-S: sequent-polymorphic finitary contracts for iPRA

This archive develops **KIFC-S**, a compositional refinement of the KIFC-R
framework for embedding finite, quantitative mathematics into intuitionistic
primitive recursive arithmetic.

Repository snapshot: `7fa3ba48e8f62e8018ed954faaa48b908217eaf1`
(16 November 2026).

## Main contribution

The central interface is the open contract

```text
Contract A phi :=
  for every context Delta,
  proofs in Delta of all formulas in A produce a proof in Delta of phi.
```

The report proves constructively that `Contract A phi` is exactly equivalent
to the ordinary sequent `A |- [PRAAx] phi`.  The contract form is useful for
proof generation because it is independent of one preassembled ambient
context.  It supports composition by simultaneous cut, substitution at open
parameters, residual-boundary discharge, and query-specialized graph
compilation.

The package also integrates:

- least backward proof slices and residual frontiers for multiple queries;
- two-sided finite strategy certificates for fixed bounded quantifier
  alternation;
- a small normalized trace-reflection candidate using `PRA.qfInd`;
- acyclic and capped-cyclic precision demand;
- finite relational viability and stable-observer elimination;
- a coherence trichotomy separating finite use, coherent paths, and regular
  metric names;
- guarded operations, finite nets, height-bounded enumeration, and backend
  transport.

## Contents

- `paper/ipra_kifcs_framework.pdf` - compiled report.
- `paper/ipra_kifcs_framework.tex`, `paper/sections/*.tex` - LaTeX source.
- `lean/KIFCS/OpenContract.lean` - no-placeholder candidate for the central
  contract calculus.
- `lean/KIFCS/NormalizedTrace.lean` - no-placeholder normalized trace
  candidate.
- `lean/KIFCS/*Blueprint.lean` - typed formalization blueprints.
- `lean/FORMALIZATION_PLAN.md` - dependency-ordered completion plan.
- `reference/kifcs_reference.py` - exact finite reference algorithms.
- `reference/test_kifcs_reference.py` - regression and property tests.
- `examples/*.json` - graph, demand, relation, and strategy examples.
- `metadata/THEOREM_LEDGER.md` - claim-by-claim status.
- `metadata/DIFFICULTY_RESOLUTION.csv` - obstacle and residual matrix.
- `metadata/SOURCE_AUDIT.md` - repository and prior-framework audit.
- `metadata/framework_schema.json` and `metadata/proof_status.json` -
  machine-readable descriptions.
- `validation/` - build, test, preflight, and visual-audit records.

## Exact status

- Human mathematics: complete for the generic theorem schemas stated in the
  report.
- Inherited Lean results: identified by path and pinned commit; not rebuilt in
  this artifact container.
- `OpenContract.lean` and `NormalizedTrace.lean`: source-oriented,
  no-placeholder candidates, but not compiled here because Lean is not
  installed in the artifact runtime.
- Larger Lean files: explicit blueprints and proof-bearing interfaces; no
  theorem-specific `axiom`, `sorry`, or `admit` is used.
- Python: exact tests are run by `build.sh`.
- PDF: compiled with pdfLaTeX, preflighted, rendered, and visually inspected.

The package does **not** claim general effective Faltings, Siegel, Roth,
Mordell-Weil generation, unrestricted exact branch selection, or effective
analytic constants.  It states the exact residual producer formulas needed by
such applications.

## Reproduction

From the archive root:

```sh
./build.sh
```

Lean validation requires placing `lean/` in a checkout of the pinned ProveIt
repository and following `lean/FORMALIZATION_PLAN.md`.

No checksum manifest is included.
