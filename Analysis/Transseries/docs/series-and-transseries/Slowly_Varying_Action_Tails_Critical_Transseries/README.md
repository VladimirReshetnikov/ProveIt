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
- `verification/results.json`: complete recorded outputs and checks (filed as delivered, without a final newline).
- `verification/*.csv`: coefficient, cutoff, and inverse-chart numerical data.
- `verification/*_table.tex`: the tables input by `article.tex`.
- `verification/environment.txt`: tested Python version and dependency versions.
- `verification/validation_summary.txt`: build and numerical cross-check results.
- `requirements.txt`: Python dependency versions from the tested environment.
- `SOURCE_MANIFEST.md`: pinned repository paths and primary literature sources.
- `Makefile`: build, exact-check, and full-verification commands.
- The delivered checksum ledger `SHA256SUMS.txt` was verified in full on
  filing (17/17, batch 50) and not kept; the delivered archive remains in the
  repository history (see `docs/incoming/README.md`, batch 50 row).

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
python verification/make_tables.py --input rerun/results.json
```

To put a fresh run in a different directory without replacing the archived
outputs, use `--output-dir PATH`. The `--quick` option uses fewer indices and
is suitable for diagnostics, but its output does not contain all rows of the
published tables. Do not regenerate the full tables from quick-run data.

(Editorial, 2026-09-29: as delivered, `verify.py` wrote into `verification/`
unless given `--output-dir`, quick runs included, and `make_tables.py`
always rewrote the three tables that `article.tex` inputs. Both now write
into `rerun/` in the package root by default; writing into `verification/`
requires `--overwrite-recorded`, and `make_tables.py` reads `--input`
(default: the recorded `verification/results.json`). `make verify` writes
into `rerun/`. On Windows use `py` instead of `python`, or
`uv run --no-project --with numpy==2.3.5 --with scipy==1.17.0 --with
mpmath==1.3.0 --with sympy==1.14.0 python verification/verify.py`.)
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

## Editorial amendments (ProveIt, 2026-09-29)

Filed on 2026-09-29 (batch 50 of `docs/incoming/`; see `docs/incoming/README.md`).
The following changes were made; every change to the article source is
preceded by a `% ed. (2026-09-29)` comment, the visible additions are labelled
"Editorial note (ProveIt, 2026-09-29)" or "Editorial addition", and no label
was renamed.

- `article.tex`:
  - an unnumbered `ednote` environment (no numbering shifts);
  - after the provenance paragraph of Section 1.1: the logarithmic-endpoint
    package `../Logarithmic_Critical_Endpoint_Lambert_Charts/` (in this
    article's snapshot, uncited by name) treats the `alpha = 2` analogue of
    the logarithmic tails at leading order (`thm:weightedchart`,
    `thm:weightedbudget`), its Lambert core has the form of `eq:Lambertcore`
    at `(alpha, m) = (2, 1)`; the marginal package's `thm:min-budget` is the
    `alpha = 2` two-term budget; the confluent and stable–Gaussian packages
    treat the crossover `alpha -> 2` for exact tails; none treats
    `1 < alpha < 2` with a slowly varying factor;
  - after `eq:Hs`: the normalization dictionary with the critical Hahn
    article (`b_n^CHT = Gamma(-alpha)^(1/alpha) b_n`,
    `L = s Gamma(-alpha)^(-1/alpha)`, `lambda^CHT = Gamma(-alpha)^(-1/alpha) lambda_n`;
    `Phi_alpha` is its `R_alpha`), under which `thm:cutoff` and `thm:budget`
    at `l = 1` are that article's (checked at `alpha = 3/2`, `s = 0.99975`:
    0.357773962623 both ways);
  - research question 5: the same slowly varying limits near `alpha = 2` are
    asked by the logarithmic-endpoint (Q6), marginal (Q2), stable–Gaussian
    (Q3) and confluent (Q4) packages; none is answered;
  - the reproduction commands in the appendix now pass `--input
    rerun/results.json` to `make_tables.py`;
  - bibliography entries `ed:lce`, `ed:mct`, `ed:cct`, `ed:sge`, placed after
    the delivered ones (widest label `99`), so no delivered reference is
    renumbered.
- `article.pdf`: rebuilt with three pdfLaTeX passes (23 pages, unchanged; no
  errors, undefined references, multiply defined labels, duplicate
  destinations, overfull or underfull boxes; every font Type 1).
- `verification/verify.py`: default `--output-dir` is `rerun/`, with
  `--overwrite-recorded` required for `verification/`; CSV rows are written
  with LF (the `csv` default wrote CRLF on every platform) and `results.json`
  with LF and a final newline. `--exact-only` (552 assertions) writes nothing,
  as delivered.
- `verification/make_tables.py`: `--input`, `--output-dir` (default
  `rerun/`) and `--overwrite-recorded`; tables written with LF. Run on a copy
  from the recorded `results.json`, it reproduced the three filed tables byte
  for byte.
- `Makefile`: `verify` passes `--input rerun/results.json` to
  `make_tables.py`.
- A full rerun on a copy wrote LF files into `rerun/`; `inverse.csv` equals the
  filed one byte for byte, while `coefficients.csv` (3 lines), `cutoffs.csv`
  (16 lines) and `results.json` (24 lines, and the new final newline) differ
  only in the last digits of double-precision values, as for the delivered
  program. The recorded `verification/` files are unchanged (the three CSVs
  were normalized from CRLF to LF on filing).
- `verification/validation_summary.txt`, `verification/environment.txt` and
  `SOURCE_MANIFEST.md` are kept as delivered.
- `README.md`: this section, the ledger and `results.json` bullets, and the
  note under "Running the checks".
