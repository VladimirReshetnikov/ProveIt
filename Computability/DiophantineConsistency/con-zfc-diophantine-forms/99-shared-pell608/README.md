# Shared arithmetic witnesses for direct ZFC-consistency quartics

This contribution gives a fully materialized ordinary quartic whose absence
of natural solutions is provably equivalent in ZFC to syntactic Con(ZFC),
together with an unrestricted-integer companion.

| Domain | Unknowns | Quadratic residuals | Expanded monomials | Exact degree | Maximum absolute coefficient |
|---|---:|---:|---:|---:|---:|
| Nonnegative integers | 608 | 491 | 7,582 | 4 | 79,824,571 |
| Unrestricted integers | 1,685 | 850 | 12,082 | 4 | 79,827,802 |

The natural polynomial is the sum of the squares of every residual in
artifacts/natural/equation.json. All 491 residuals are also printed in
report.pdf. Expanded literal polynomials are supplied for both domains.
No variable exponent, factorial, binomial, Pell sequence, or bounded
quantifier remains in either exported polynomial.

## Contribution

The direct numerical C222 proof-calculus source is inherited. New changes
relative to the inspected 3,614-natural-variable incoming construction are:

- Cofinal beta digit bounds remove two local remainder coordinates.
- A certified fixed-power majorant avoids a duplicate source evaluation.
- One digit radix serves all 14 binomial graphs.
- One simultaneous Pell environment serves all 25 positive power graphs;
  20 distinct literal exponent atoms share their index certificates.
- The factorial radius is its candidate output times the square of its input.
- Exact affine and terminal nonlinear eliminations preserve quadratic rows.

The reduction from 3,614 to 608 naturals is 83.18%. This is a result in the
direct proof-calculus quartic branch. It does not beat the repository's
few-variable branches, and does not assert global optimality or worldwide
priority. Witness sizes can grow enormously.

## Contents

- report.tex, its three TeX inputs, and report.pdf: complete report,
  ordinary proofs, literal equation, and exact guard index set.
- src/: deterministic standard-library Python construction.
- artifacts/natural/: raw system, affine export, elimination trace,
  final residual system, and expanded polynomial.
- artifacts/natural/integer/: unrestricted-integer equation and guards.
- tests/: independent finite verifiers and arithmetic controls.
- reviews/: independent mathematical reviews and execution receipts.
- provenance/: pinned source interfaces, inherited notices, comparison
  data, and inspected Mathlib Pell source.
- MANIFEST.sha256: hashes of the distributed files.

## Reproduce

Run from this directory with Python 3:

    python3 verify_all.py
    python3 -O verify_all.py

These rebuild nine defining artifacts in a temporary directory and compare
them byte for byte, verify all elimination and guard identities, check every
arithmetic macro interface, parse the printed equation back to its literal
polynomial, and run independent lemma controls.

To create output copies:

    python3 src/build.py --output /tmp/con-zfc-natural
    python3 src/integer_export.py --input /tmp/con-zfc-natural

To compile:

    pdflatex -interaction=nonstopmode -halt-on-error report.tex
    pdflatex -interaction=nonstopmode -halt-on-error report.tex

Monomial indices are zero-based. The record [c,[i,j,j]] means c*x_i*x_j^2;
an empty index list denotes a constant.

## Proof status

The report gives the ordinary unbounded equivalence proof, composing the
inherited C222/ZF/ZFC calibration with classical Pell arithmetic and the new
simultaneous-certificate lemmas. These arguments are formalizable in ZFC.
Finite code checks are separate from those unbounded proofs.

No new complete Lean/Rocq theorem or object-language ZFC proof object is
included. Existing Lean files are provenance copies, not a standalone
formalization project. Neither Con(ZFC) nor its negation is proved.

Repository audit pin: 8b328dc1801a506cdf448798702192a1d8d96f18.
Inherited calibration pin: 08200eb10fde2db408c69dffd840d6920a569b1f.
No repository write or publication was performed.
