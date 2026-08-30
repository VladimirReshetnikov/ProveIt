# Local, Boundary, and Reciprocal Expansions of q-Analogues

This package contains a standalone research report extending the expansion
material in Vladimir Reshetnikov's ProveIt monograph on q-Pochhammer symbols and
q-binomial coefficients.

## Contents

- `q_analog_expansions_report.tex` — complete LaTeX source.
- `q_analog_expansions_report.pdf` — compiled 56-page report.
- `q_expansion_experiments.py` — commented exact-symbolic and high-precision
  numerical verification program.
- `numerical_results.txt` — output of the included verification run.
- `MANIFEST.sha256` — SHA-256 checksums for the four primary files and this
  README.

## Scope

The report develops expansions and coefficient-generation methods for:

- finite q-Pochhammer symbols at arbitrary regular or resonant centers;
- finite products and scaled factors as q approaches 1;
- Gaussian and q-multinomial coefficients, including all logarithmic
  coefficients and ordinary `(q-1)` Taylor coefficients;
- q approaching 0, positive infinity, and negative infinity;
- q approaching -1, including a closed value and first derivative of every
  Gaussian coefficient;
- arbitrary finite roots of unity via cyclotomic valuations and Bell
  polynomials;
- infinite q-Pochhammer products for fixed `a` and for coalescing `a=q^x`;
- q-gamma, q-beta, q-polygamma, q-exponentials, q-derivatives, and Jackson
  integrals;
- eta/theta modular transseries and radial root-of-unity asymptotics;
- basic hypergeometric functions as differential-operator deformations;
- the double-scaling regime `q=exp(-tau/N)`, `k=alpha*N`;
- implications for the ProveIt Fabius-function programme, conjectures, and
  formalization directions.

## Rebuilding the PDF

A recent TeX Live installation with `latexmk` is sufficient:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error q_analog_expansions_report.tex
```

## Running the checks

The program requires Python 3.10 or later, SymPy, and mpmath:

```sh
python q_expansion_experiments.py
```

The committed output was produced with 80 decimal digits of working precision.
The exact q=1 and q=-1 suites each cover all 230 pairs `0 <= k <= n <= 20`.

## Baseline source

The report was written as a self-contained companion to:

`Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/exponents-and-q-series/q_pochhammer_q_binomial_monograph/q_pochhammer_q_binomial_monograph.tex`

in the `VladimirReshetnikov/ProveIt` GitHub repository, main branch, inspected on
2026-08-30.
