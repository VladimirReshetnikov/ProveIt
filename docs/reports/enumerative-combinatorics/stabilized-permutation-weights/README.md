# Rationality and growth of stabilized permutation-weight series

Research report prepared for Vladimir Reshetnikov, September 19, 2026.

## Read first

`article.pdf` is the complete report; `article.tex` is its editable LaTeX source.
The report investigates the full stabilized generating functions of the
permutation-weight q-Eulerian polynomials, beyond their initial connection
with OEIS A256193.

The starting polynomial recurrence and stabilization are published results.
The report derives an all-d finite-spectrum theorem, rationality, a universal
integer denominator, the exact radius of convergence, and residue-class
asymptotics. The two-descent sequence has an explicit formula using powers
of 3, powers of 2, and Fibonacci numbers. The report carefully distinguishes
these results from previously established stabilization/partition results.
The mathematical arguments are presented as English proofs, not Lean proofs.
Novelty has not been exhaustively or independently certified.

## Files

- `article.tex`, `article.pdf`: article source and compiled 16-page report.
- `code/derive.py`: exact symbolic construction in Q(q), with ODE and
  initial-condition identity checks. Requires SymPy.
- `code/verify.py`: independent standard-library implementation of the
  original polynomial recurrence, plus rational-series expansion and
  closed-form checks. No symbolic algebra or floating point is used.
- `data/rational_series.json`: coprime P_d, Q_d for 1 <= d <= 6, normalized
  by Q_d(0)=1. Coefficient arrays are in ASCENDING degree order.
- `data/spectral_certificates.json`: exact exponential frequencies and
  rational amplitudes for the differential construction.
- `data/coefficients.csv`: W_d coefficients for 0 <= k <= 250, 1 <= d <= 6.
- `data/W1_coefficients.txt` ... `data/W6_coefficients.txt`: the same data
  in OEIS-style `index value` files. These are not assigned OEIS entries.
- `data/partition_comparison.csv`: a separate exact calculation of
  T(d+k,d), compared with W_d[k] through k=40.
- `data/verification.json`, `data/verification.log`, `data/derivation.log`,
  `data/rederivation_check.log`:
  actual results of the included programs.
- `requirements.txt`, `Makefile`: reproduction helpers.
- `SHA256SUMS.txt`: SHA-256 checksums for every other packaged file.

## Run the independent check without installing anything

Python 3.9 or newer:

```text
python code/verify.py --max-k 40 --export-count 251
```

This computes original-recurrence rows through n=48, independently checks
738 coefficient comparisons (six descent counts, 41 deficits, three
lengths), and checks all 251 exported coefficients for d=1,2 against their
closed forms. It rewrites the CSV, b-files, and verification JSON.
It does not change the rational-function data.

## Re-derive the rational functions

```text
python -m pip install -r requirements.txt
python code/derive.py --max-d 6 --check-only
```

`--check-only` re-derives and checks the packaged numerator/denominator
arrays. Omit this option to regenerate `rational_series.json` and
`spectral_certificates.json`. Larger descent counts are supported by the
algorithm but may incur substantial symbolic-expression growth.

The recorded derivation used SymPy 1.14.0. The derivation log's timings
are observations from this execution, not portable performance guarantees.

## Rebuild the PDF

A TeX Live installation with newtx, Source Sans Pro, tcolorbox, and the
usual AMS/LaTeX packages is sufficient:

```text
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

On systems with `make`, use `make pdf`, `make verify`, or `make derive`.
No external reference PDFs or font files are required in this directory.

## Interpretation of the verification

Theorems in the report apply to every d and every relevant index. Finite
computation is not the proof of those theorems; it is an independent audit
of explicit formulas, implementation, normalization, and indexing.
No proof-assistant verification is claimed. No open conjecture of the
original papers is silently assumed by the rationality or growth proofs.
