# Local, Boundary, and Reciprocal Expansions of q-Analogues

This package contains a standalone research report extending the expansion
material in Vladimir Reshetnikov's ProveIt monograph on q-Pochhammer symbols and
q-binomial coefficients.

## Contents

- `q_analog_expansions_report.tex` — complete 2,777-line LaTeX source.
- `q_analog_expansions_report.pdf` — compiled 57-page report.
- `q_expansion_experiments.py` — commented exact-symbolic and high-precision
  numerical verification program.
- `numerical_results.txt` — output of the included verification run.
- `MANIFEST.sha256` — SHA-256 checksums for the four primary files and this
  README, refreshed after the post-publication Lean crosswalk update.

The delivered archive baseline was a 56-page, 2,708-line report. All five
submitted payload hashes verified on arrival. The later exact Lean crosswalk
added the denominator-free commutative-ring value theorem and its status
boundary; the paired PDF and checksum ledger were then rebuilt and refreshed.
This records the current artifact without erasing the dimensions or integrity
of the delivered baseline.

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

## Lean crosswalk

The value half of the report's complete first-jet theorem at `q = -1` is now
formalized in the stronger setting of an arbitrary commutative ring. The
exhaustive five-theorem surface of
`FabiusFunction.GaussianBinomialAtNegOne` is
`gaussianBinomial_neg_one_even_even`,
`gaussianBinomial_neg_one_odd_even`,
`gaussianBinomial_neg_one_odd_odd`,
`finiteQPochhammerIn_neg_one_even`, and
`finiteQPochhammerIn_neg_one_odd`. Together with the reused
`gaussianBinomial_neg_one_even_odd_eq_zero` theorem from
`FabiusFunction.QBinomialReciprocity`, these declarations give all four
Gaussian parity values and the two companion finite-product identities. The
Gaussian formulas are total in all natural row and column parameters,
including columns above the row by zero extension. The focused Lake target has
been compiled successfully.

The first-derivative formulas and the resulting characteristic-zero
simple-root theorem are not yet formalized.  The report's manuscript proof is
not a substitute for those remaining Lean declarations.

## Baseline source

The report was written as a self-contained companion to:

`Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/exponents-and-q-series/q_pochhammer_q_binomial_monograph/q_pochhammer_q_binomial_monograph.tex`

in the `VladimirReshetnikov/ProveIt` GitHub repository, main branch, inspected on
2026-08-30.
