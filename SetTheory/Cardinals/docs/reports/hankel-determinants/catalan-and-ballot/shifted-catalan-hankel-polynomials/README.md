# Shifted Catalan Hankel Polynomials

**Exact coefficients, sharp recurrences, and a denominator conjecture**  
Research package, 19 September 2026.

## The mathematical object

For nonnegative integers N and m, define

    D_N^(m)(a,b) = det(a*C_(i+j+m) + b*C_(i+j+m+1))_(0 <= i,j < N),
    C_n = binomial(2*n,n)/(n+1),
    D_0^(m) = 1.

The article proves the denominator-exponent assertion on page 4 of Paul
Barry's arXiv:2011.10827v1. Its separate printed Conjecture 2 requires an
explicit one-unit shift correction, proved in Appendix A.

For b != 0 and a*(a+4*b) != 0, the **minimal** characteristic polynomial is

    (X^2 - (a+2*b)*X + b^2)^(m*(m-1)/2 + 1),

so the minimal order is m*(m-1)+2. The article supplies all exceptional
reduced denominators, the exact coefficient formula, numerator degree and
reciprocal symmetry, and a finite full two-exponential expansion.

## Status

This is an unrefereed AI-assisted manuscript. The article contains
all-parameter mathematical proofs; the finite experiments are independent
support and debugging checks, not substitutes for those proofs. No Lean
formalization or external peer review was performed. No claim of first
discovery, or of an exhaustive global determination of current open status,
is made. The source version, related literature, and limitations of the
literature search are recorded in `notes/provenance.md`.

## Files

- `article.pdf`: complete 20-page article.
- `article.tex`: self-contained LaTeX source, including the bibliography.
- `code/catalan_hankel.py`: exact standard-library Python implementation.
- `code/verify.py`: independent determinant, coefficient, recurrence,
  exceptional-case, reciprocal-symmetry, and asymptotic checks.
- `data/verification.json`: machine-readable outcome and check counts.
- `data/verification.txt`: captured console report from the verification run.
- `data/sequences.csv`: 1,395 integer values with explicit `(m,a,b,N)` columns.
- `data/coefficient_rows.json`: coefficient rows for m=0,...,8 and N=0,...,12.
- `data/generating_functions.json`: uniform numerator/denominator arrays for
  m=0,...,7 and four nonexceptional integer parameter pairs.
- `data/minor_polynomials.json`: exact polynomials M_(m,ell)(N), m=0,...,7.
- `data/two_branch_polynomials.json`: exact polynomial multipliers of 4^N
  and 1^N for a=1, b=2, m=0,...,7.
- `notes/provenance.md`: primary sources, version audit, and novelty scope.
- `Makefile`: optional test, PDF-build, and cleanup commands.

## Reproduce the computations

Use Python 3.10 or later. There are no third-party Python dependencies.
Run from this directory:

```sh
python3 code/verify.py --out data
python3 code/catalan_hankel.py 8 3 --a 2 --b 3 --direct
```

The first command regenerates the data files and prints its verification
report. To refresh the captured text report as well:

```sh
python3 code/verify.py --out data > data/verification.txt
```

Do not use `python -O`: the verification program intentionally uses
assertions. The supplied run completed successfully using exact integers
and rational numbers. The public numerical routines are designed for
integer a,b; the theorems in the article apply more generally to complex
parameters. The arithmetic operation count of coefficient generation is
O(N+m^2), not a bit-complexity bound.

Example from Python, with `code` on the import path:

```python
from catalan_hankel import coefficients, hankel_formula, hankel_direct
from catalan_hankel import generating_function, minimal_denominator

assert coefficients(3, 2) == (30, 54, 27, 4)
assert hankel_formula(3, 2, 1, 1) == 115
assert hankel_direct(3, 2, 1, 1) == 115
p, q = generating_function(2, 1, 1)
assert p == [1, 1]
assert q == [1, -6, 11, -6, 1]
assert minimal_denominator(2, -4, 1) == [1, 3, 3, 1]
```

`generating_function` deliberately returns the **uniform**, potentially
unreduced representation at exceptional parameters. It retains trailing
zero coefficient positions. `minimal_denominator` handles the exceptions.

## Data conventions

Every polynomial array is in ascending power order.

- In `coefficient_rows.json`, entry k is the coefficient of a^k*b^(N-k),
  not a^(N-k)*b^k.
- In `minor_polynomials.json`, entry j is the coefficient of N^j.
- In `generating_functions.json`, the arrays are in powers of t.
- In `two_branch_polynomials.json`, `P_plus` and `P_minus` are polynomial
  multipliers of exponential sequences. They are NOT the ordinary-
  generating-function numerator P_m from the article.
- Rational coefficients are strings such as `"8/3"`, never rounded decimals.
- Negative indices in the minor tests use polynomial binomial coefficients.

## Build the PDF

A reasonably complete TeX Live installation with `newtx`, `mathtools`,
`amsthm`, `microtype`, `geometry`, `hyperref`, and the other standard packages
listed in the preamble is sufficient:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively, run `pdflatex` repeatedly until references stabilize.
The PDF was built and its rendered pages inspected. Font packages are
referenced through the local TeX installation; no font files are included
in this archive. The package also omits third-party article PDFs, compiler
logs, bytecode, and checksum files.
