# Slowly Varying Critical Transseries

**Universal action budgets, convergent Lambert charts, and an effective-index expansion**

Research article prepared for Vladimir Reshetnikov, September 29, 2026.
The PDF contains 23 pages. The LaTeX source and every generated table fragment
needed to rebuild it are included.

## Research target and scope

This article addresses Research Question 1, "Slowly varying action tails," in
ProveIt's *Beyond Finite-Action Folds: Critical Hahn Transseries, Stable Sector
Asymptotics, and Sharp Action Budgets*. The inspected repository snapshot is
`ebd8344bca77d8352cd745b7df374618a290a029`.

The model is `U_beta(q) = beta A(q exp(U_beta(q)))`, with nonnegative weights
`a_j ~ a j^(-1-alpha) ell(j)`, `1 < alpha < 2`. The general results give the
critical inverse scale, a stable local coefficient law, a universal cutoff
profile, a sharp necessary-and-sufficient lossless-cutoff criterion, and a
conditional large-action point-process law.

An explicit oscillatory slowly varying tail shows that these probability and
inverse-scale laws do not automatically imply a power-log transseries chart.
For eventual exact logarithmic tails `a j^(-1-alpha) (log j)^m`, integer `m >= 1`,
the article gives a convergent analytic chart over a Lambert W_-1 core and
all fixed orders of an inverse-logarithmic coefficient/cutoff expansion.
Its first correction is a shift to the effective stable index
`alpha - m/log(b_n)`, at fixed normalized coordinates. A strictly positive
cutoff derivative yields a two-term asymptotic minimum-budget formula.

The general regular-variation and stable-limit machinery is classical and is
credited as such. The paper supplies its own proofs for the stated model.
Historical publication novelty has not been independently established; no
claim to have solved an unrestricted transseries-realization problem is made.
The exponent is fixed in the interior `(1,2)`. Endpoint uniformity, growing
coupling windows, and fully effective finite-n error bounds are not claimed.
Ten concrete further research questions are included.

## Contents

- `article.pdf`: compiled article.
- `article.tex`: complete LaTeX source, with inline bibliography.
- `verification/verify.py`: exact algebra checks and numerical diagnostics.
- `verification/make_tables.py`: regenerates the three input table fragments.
- `verification/results.json`: complete recorded outputs and checks.
- `verification/*.csv`: coefficient, cutoff, and inverse-chart numerical data.
- `verification/*_table.tex`: the tables input by `article.tex`.
- `verification/environment.txt`: tested Python version and dependency versions.
- `verification/validation_summary.txt`: build and numerical cross-check results.
- `requirements.txt`: Python dependency versions from the tested environment.
- `SOURCE_MANIFEST.md`: pinned repository paths and primary literature sources.
- `Makefile`: build, exact-check, and full-verification commands.
- `SHA256SUMS.txt`: checksums of the delivered files, excluding itself.

## Rebuilding the article

Run from this directory. A LaTeX installation with the standard packages used
in the preamble is required; the recorded PDF was produced by pdfLaTeX.

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

The recorded table fragments are already present. A PDF rebuild does not
require Python or a new numerical run.

## Running the checks

Use a Python environment compatible with the pinned dependencies, then run:

```sh
python -m pip install -r requirements.txt
python verification/verify.py --exact-only
```

This runs 552 exact algebra assertions without changing the recorded data.
The checks cover finite Lagrange/feedback coefficient identities, literal
cutoff dependence and monotonicity, two chart coefficient identities, and the
Bell-polynomial recurrence. They do not prove infinite analytic statements.

For the full numerical run, including the largest coefficient index 65536:

```sh
python verification/verify.py
python verification/make_tables.py
```

To put a fresh run in a different directory without replacing the archived
outputs, use `--output-dir PATH`. The `--quick` option uses fewer indices and
is suitable for diagnostics, but its output does not contain all rows of the
published tables. Do not regenerate the full tables from quick-run data.
The full run has FFT working memory proportional to the largest index and
also performs high-precision quadrature and a separate positive recurrence.

## What was checked

The 552 exact assertions passed. The full numerical run was completed through
`n = 65536`. The FFT coefficient at `n = 256` was compared to a separate
65-digit positive recurrence; the measured relative discrepancy was about
`3.95e-15`. Repeating cutoff quadrature with 96 and 160 Gauss-Jacobi nodes gave
a maximum measured difference of about `7.95e-15` at the tested points.
These are numerical cross-checks, not uniform error bounds or interval proofs.

The PDF compiled with no LaTeX warnings, unresolved citations/references, or
overfull boxes on the final pass, and its rendered pages were visually checked.
No Lean formalization is included, and no analytic theorem in the article is
represented as having been checked by a proof assistant. The numerical values
are not outward-rounded certificates. The asymptotic minimum-budget formula
is not a certified finite-n selector without explicit remainder constants.

No files in the upstream repository were changed.
