# Inverse q-Analogs in All Parameters

This archive contains a standalone 104-page research report extending the
`exponents-and-q-series` drafts in the ProveIt repository.  It develops local,
singular, endpoint, cyclotomic, and multivariate inverse theory for finite and
infinite q-Pochhammer symbols, Gaussian and multinomial coefficients,
q-numbers, q-factorials, q-gamma, q-digamma, q-beta, Euler q-exponentials,
basic hypergeometric series, theta functions, and a geometric random-series
family containing the Rvachev/Fabius distribution.

## Main files

- `inverse_q_analogs_extended_report.tex` — complete LaTeX source.
- `inverse_q_analogs_extended_report.pdf` — rendered report.
- `inverse_q_analogs_experiments.py` — commented symbolic/numerical experiment
  program; it regenerates every table, CSV file, and figure.
- `requirements.txt` — Python dependencies.
- `numerical_summary.txt` — compact record of the generated experiments.
- `numerical_results.tex` — generated table fragment included by the report.
- `data/` — exact and high-precision CSV output.
- `figures/` — PDF vector figures and PNG previews.
- `SHA256SUMS` — checksums for all other files in the archive.

## Principal extensions developed in the report

1. A common Bell-polynomial and Lagrange-Good calculus for partial inverses in
   any selected parameter, with Jacobian identifiability and condition numbers.
2. Newton-Puiseux and Newton-polygon treatment of critical, fractional-power,
   and mixed-scale inverse branches.
3. A complete q=-1 critical classification for finite `(a;q)_n` base slices,
   including the exact cubic at `n=3, a=-1/3` and its full two-parameter Morse
   geometry.
4. Explicit radial inverse normal forms at arbitrary primitive roots of unity,
   with the first constant and linear corrections written as convergent
   cyclotomic Lambert sums.
5. Base, argument, order, upper-parameter, lower-parameter, and simultaneous
   inverses for q-Pochhammer and Gaussian families, including q=0, q=1,
   q=-1, roots of unity, and q=infinity.
6. Parameter inverses and degeneracy strata for q-gamma, q-digamma, q-beta,
   q-exponentials, basic hypergeometric functions, and theta/nome maps.
7. Exact variance- and kurtosis-based recovery of the contraction ratio in a
   generalized Fabius-Rvachev family, plus a program for CDF and quantile
   inverse branches.
8. Branch-aware continuation, real and complex certification, interval-Newton
   and Rouche tests, a formula atlas, a Lean formalization roadmap, and
   concrete conjectures/research problems.

Statements are explicitly marked as proved, symbolic/numerical, or
conjectural.  Numerical evidence is not presented as proof.

## Source drafts consulted

The report was prepared against the `main` branch state at commit
`23b19a515ceb44a513b1ec56aeb5c9e99dda5952` (2026-08-30), especially:

- `Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/exponents-and-q-series/q_pochhammer_q_binomial_monograph/q_pochhammer_q_binomial_monograph.tex`
- `.../q_pochhammer_q_binomial_expansions_report/q_analog_expansions_report.tex`
- `.../inverse_q_analogs_report/inverse_q_analogs_report.tex`
- `.../Exponents_and_q_Series_Frontiers/Exponents_and_q_Series_Frontiers.tex`
- related Fabius/Rvachev reports and numerical assets in the same draft tree.

The report is self-contained; those files are not required to compile it.

## Reproducing the numerical work

Python 3.10 or newer is recommended.

```bash
python -m venv .venv
# Linux/macOS:
. .venv/bin/activate
# Windows PowerShell:
# .venv\Scripts\Activate.ps1

python -m pip install -r requirements.txt
python inverse_q_analogs_experiments.py
```

The program uses 80-decimal-digit mpmath arithmetic for transcendental tests
and SymPy exact arithmetic for rational/polynomial identities.  It writes 94
rows of data and regenerates all PDF/PNG figures.

## Compiling the report

A recent TeX Live or MiKTeX installation with `latexmk` is sufficient.

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  inverse_q_analogs_extended_report.tex
```

The source prefers Libertinus when installed and falls back to Latin Modern.
Python is not needed to compile the already-generated archive.
