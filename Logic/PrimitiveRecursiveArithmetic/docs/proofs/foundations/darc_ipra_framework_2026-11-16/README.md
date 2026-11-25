# DARC-iPRA

**Demand-Aware Residualizing Compilation for intuitionistic primitive recursive arithmetic**

This package develops a general framework for compiling fixed finitary mathematical arguments into the canonical ProveIt object-theory judgment

```lean
Prf PRAAx Γ φ
```

The repository audit is pinned to `VladimirReshetnikov/ProveIt` commit
`2ef31aa3e313d792df6b63bb28babfe48e1f982e` (2026-11-16).

The [repo-wide iPRA unification plan](../../../../UNIFICATION-PLAN.md)
describes the shared proof interface and how research packages enter the
main derivation library.

## Main contribution

DARC unifies four forms of backward analysis in one finite product lattice:

1. which certificate fields must escape their local existential scope;
2. which approximation precisions are actually demanded;
3. which guards, apartness margins, or separation hypotheses are needed;
4. which unproved quantitative producers must remain as explicit residual hypotheses.

The least prefixed point of the resulting monotone transfer network determines a query-specialized theorem and proof schedule. Internal witnesses are sealed by existential elimination, named witnesses use bounded least search only when demanded, bounded loops are reflected by quantifier-free induction, and every fixed formula/program is statically specialized to concrete primitive-recursive symbols. No total universal evaluator is assumed.

## Contents

- `paper/darc_ipra_framework.tex` and `paper/sections/` — complete LaTeX source.
- `paper/darc_ipra_framework.pdf` — compiled report.
- `lean/DARC/StructuralKernel.lean` — source-oriented, no-placeholder structural kernel using the current `Prf PRAAx` API.
- `lean/DARC/*.lean` — dependency-ordered formalization blueprints for demand closure, bounded reflection, traces, relational viability, and the compiler.
- `lean/FORMALIZATION_PLAN.md` — a concrete route to a complete Lean development.
- `reference/darc_reference.py` — exact finite reference algorithms.
- `reference/test_darc_reference.py` — regression/property tests.
- `reference/generate_demo.py` and `examples/demo.json` — generated worked example.
- `examples/sample_plan.json` and `schema/darc_plan.schema.json` — validated machine-readable plan instance and schema.
- `metadata/` — theorem ledger, difficulty matrix, claims, and source audit.
- `schema/darc_plan.schema.json` — machine-readable plan format.
- `validation/` — test, build, PDF, and render records.

## Verification status

- The generic mathematical arguments in the report are developed in full at the human-proof level.
- The structural Lean kernel contains no `sorry`, `admit`, or new axioms, but could not be elaborated here because the artifact runtime has no Lean executable.
- The larger Lean files are explicit blueprints and contain marked `sorry` milestones.
- Python tests validate only the finite metalevel algorithms; they are not iPRA proofs.
- No new Lean-kernel-checked theorem is claimed.
- Deep theorem-specific producers—general effective height bounds, unrestricted branch selectors, global convergence moduli, and similar inputs—remain explicit residuals.

## Reproduce

From the package root:

```bash
bash build.sh
```

This runs the Python tests, regenerates the demonstration, compiles the PDF, and records PDF metadata. Lean integration requires a checkout of the pinned ProveIt repository and the steps in `lean/FORMALIZATION_PLAN.md`.
