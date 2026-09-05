# Recurrence-Free Dyadic Formulae for the Fabius and Rvachev Functions

## Contents

- `dyadic_closed_forms.pdf` — the 23-page article, including complete proofs,
  formula comparisons, examples, source references, and implementation notes.
- `dyadic_closed_forms.tex` — self-contained LaTeX source; no external bibliography,
  figures, repository notation files, or other inputs are required.
- `verify.py` — standard-library exact-arithmetic implementations and cross-checks.
- `verification.json` — results of the completed default verification run.

## Principal formula families

The article gives fully explicit Bernoulli-partition and positive-composition
coefficients, a binary-digit telescope, an integer bordered determinant, and a
moment-free quarter-base formula. The latter uses only floor(n/2)+1 centered
finite uniform splines for an argument a/2^n. It also gives direct Rvachev density
extraction, derivatives, iterated primitives, and a reciprocal-integer-base
extension. Existing ingredients are distinguished from the deductions presented
here; no blanket historical-priority or new Lean-formalization claim is made.

## Conventions

F is the bounded CDF of sum(U_j/2^j), j >= 1, with U_j uniform on [0,1].
The Rvachev bump up is the density of 2X-1 and satisfies
up(t) = F(1-abs(t)) on [-1,1], and zero outside. The signed global extension
is a separate function. The article states the exact folding rules.

Every auxiliary coefficient in a final value formula is a finite sum or product.
Moment relations occur in proofs, but no evaluator requires a moment recurrence.
The included implementations use memoization only to cache explicit finite sums.

## Build the PDF

Use a reasonably complete TeX Live or MiKTeX installation:

    latexmk -pdf -interaction=nonstopmode -halt-on-error dyadic_closed_forms.tex

Alternatively, run pdflatex three times. The source uses Libertinus when that
package is installed and falls back to Latin Modern otherwise. No font files
are distributed. A different font fallback can change pagination.

## Reproduce the exact tests

Python 3.9 or later; no third-party packages are needed:

    python verify.py --json verification.json

The default run checks five evaluation methods on all 520 numerator/depth pairs
0 <= a <= 2^n, 0 <= n <= 8, including unreduced dyadic representations. It also
checks reflection and refinement, nine centered coefficients, eight standard
reciprocal-power values, 360 exact centered-cutoff identities, 132 direct bump
cases, 65 half-base shift cases, and 1252 integer-base cases.

All values are integers or fractions.Fraction objects. No floating-point
comparisons or numerical tolerance are used. These are implementation checks,
not substitutes for the mathematical proofs in the article.

A larger complete-grid depth can be selected with `--max-depth`; this increases
runtime exponentially. The other test ranges are intentionally fixed.

Example imports:

    from verify import fabius_quarter, fabius_moments, up_quarter

    assert str(fabius_quarter(1, 4)) == "143/2073600"
    assert fabius_quarter(3, 3) == fabius_moments(3, 3)
    assert str(up_quarter(1, 2)) == "67/72"

The minimal evaluator printed in the article was separately extracted and
checked on the same 520 dyadic grid cases.

## Repository comparison snapshot

Repository: VladimirReshetnikov/ProveIt
Commit: 2c6baf6738a5fbf3981a27141950edbe5952b03c
Primary TeX blob: c5982d732a3caa769547e079efce37d25fb84a4e

The bibliography identifies the primary exposition, its archived dyadic-web
companion, Arias de Reyna's papers, Haugland's evaluator, Reshetnikov's 2019
half-base formula, and the elementary special-function identities used.
