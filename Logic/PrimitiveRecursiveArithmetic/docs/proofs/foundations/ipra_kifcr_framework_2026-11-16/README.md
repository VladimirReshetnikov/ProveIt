# KIFC-R: residualized finitary compilation for iPRA

This archive develops **KIFC-R**, an updated proof-compilation framework for
embedding finitary mathematics into intuitionistic primitive recursive
arithmetic.

The framework is rebased on ProveIt commit
`31784f0710fa04ccd8ee863ce9bad91fb1d8cf88`. It reuses the current checked
`IPRADerivations` library—especially bounded least search, pairing,
simultaneous recursion, arithmetic, sums, descent, and linear algebra—and
focuses new work on the remaining shared layer:

1. fixed-formula Boolean reflection;
2. proof schedules and query-specialized traces;
3. explicit residual producer formulas;
4. acyclic and capped-cyclic demand closure;
5. finite relational viability;
6. exact, metric, and gap-guarded observers;
7. guarded analytic, finite-net, and height-enumeration interfaces.

The canonical compiler endpoint is a conditional object-theory derivation

```text
B₁, …, Bᵣ, Γ ⊢[PRAAx] Φ
```

where each `Bᵢ` is an exact unresolved producer obligation such as a height
cutoff, separation gap, finite-cover margin, or effective constant. Supplying
actual derivations of the residuals closes the theorem by simultaneous cut.

## Contents

- `paper/ipra_kifcr_framework.pdf` — compiled human-readable report.
- `paper/ipra_kifcr_framework.tex`, `paper/sections/*.tex` — complete LaTeX.
- `lean/KIFCR/*.lean` — current-API Lean structures and formalization
  blueprints, including the stable cubic benchmark.
- `lean/FORMALIZATION_PLAN.md` — dependency-ordered implementation plan.
- `reference/kifcr_reference.py` — exact finite reference algorithms.
- `reference/test_kifcr_reference.py` — 19 regression/property tests.
- `examples/*.json` — graph/relation/demand examples.
- `metadata/THEOREM_LEDGER.md` — claim-by-claim status.
- `metadata/difficulty_matrix.csv` — obstacle, repair, and residual boundary.
- `metadata/framework_schema.json` — machine-readable node schema.
- `metadata/proof_status.json` — machine-readable artifact status.
- `metadata/SOURCE_AUDIT.md` — current repository and prior-art audit.
- `validation/` — tests, PDF build, preflight, render, and source scans.
- `MANIFEST.sha256` — integrity manifest.

## Exact status

- Human mathematics: developed in the report, including residual compilation,
  capped demand closure, viability, stable observers, guards, finite nets, and
  height/list conversion.
- Inherited Lean results: current checked repository modules, identified by
  path and commit; not rebuilt in this artifact.
- New Lean modules: source-oriented outlines only. Lean is unavailable in the
  artifact environment, so no new-module build is claimed. The outlines use no
  `sorry` or theorem-specific `axiom`; unfinished results are proof-bearing
  structures plus explicit implementation plans.
- Python: 19 exact tests pass.
- PDF: compiled with pdfLaTeX, preflighted, text-inspected, rendered, and
  visually audited.

## Reproduction

From the archive root:

```sh
python3 -m unittest -v reference/test_kifcr_reference.py
./build.sh
```

The report deliberately does not claim general effective Faltings, Siegel,
Roth, Mordell–Weil generation, Chebotarev, Siegel–Walfisz, or
Bombieri–Vinogradov. It supplies reusable finite verifiers and identifies the
exact quantitative producer formulas required to close those applications.
