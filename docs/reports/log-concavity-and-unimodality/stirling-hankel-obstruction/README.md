# A uniform Hankel obstruction for higher-order Stirling subset polynomials

**Main result:** a proof of the higher-order negative assertion in Deb–Sokal
Conjecture 1.4(d), with a stronger theorem for every positive shift.

Read **article.pdf** (complete article) or edit **article.tex**.

## Result

Let S^(r)_(n,k) count partitions of n+(r−1)k labelled elements into k blocks,
each of size at least r, and let s_(r,n)(x) be the row-generating polynomial.
For every integer r >= 3 and a >= 1,

    H_(r,a)(x) = det(s_(r,a+i+j)(x))_(0 <= i,j <= 2)

has all coefficients below x^5 equal to zero, and its coefficient of x^5 is
strictly negative. At the first shift it is

    -binomial(2r−1,r−1)^2 * (r−2)(r−1)(r^2+11r+6)
    / ((r+1)(r+2)^2(r+3)).

Thus the polynomial sequence fails coefficientwise Hankel total positivity
at every r >= 3. The already-known positive cases r=1,2 complete the cutoff;
those positive cases are not claimed as new results.

The article also proves a general shifted coefficient formula, an explicit
negative bound, small-positive-x obstructions to Stieltjes and Hamburger
moment representations, and asymptotic estimates. The shift-one witness
was already proposed in Appendix C of Deb and Sokal's paper; the present
contribution is its uniform proof and the all-shifts extension.

## Why this is not a manifest duplicate

The supplied manifest's entry “A sharp order-five threshold for higher-order
Stirling subset log-concavity” concerns Conjecture 1.4(c), a statement about
individual rows. This article concerns Conjecture 1.4(d), about Hankel minors
across rows. It uses none of the proof claims in the manifest.

## Reproduce the exact checks

Requires Python 3.9+ and no external packages:

```sh
python code/verify.py
```

This writes deterministic records to `data/` and prints the summary.
It works from any current directory. An alternative output directory is
available with `--outdir PATH`.

The executed checks include 270 independent partition counts, 96 complete
polynomial determinants, 1,120 degree-five determinant expansions, 100
first-shift factorizations, and 2,665 partial-binomial log-concavity checks.
They are finite audits; the proofs establish the all-parameter statements.

Optional formal rational-function check (SymPy required):

```sh
python code/symbolic_identity.py
```

The recorded symbolic run used SymPy 1.14.0. No proof-assistant check is
claimed. No floating-point sign test is used in the core verification.

## Build the PDF

A normal TeX Live or MiKTeX installation with the packages named in
`article.tex` suffices. Bibliography entries are embedded; BibTeX is not
required.

```sh
pdflatex -halt-on-error article.tex
pdflatex -halt-on-error article.tex
pdflatex -halt-on-error article.tex
```

The optional Makefile provides `make pdf`, `make verify`, and `make clean`.

## Contents

- `article.tex`, `article.pdf`: source and typeset mathematical article.
- `code/verify.py`: standard-library exact arithmetic and independent counting.
- `code/symbolic_identity.py`: optional SymPy audit of the rational factorization.
- `data/verification.json`: check coverage, exact scalar examples, root bracket.
- `data/full_determinants.json`: all 96 fully expanded determinant polynomials.
- `data/leading_coefficients.csv`: first-shift values for 1 <= r <= 100.
- `data/shifted_coefficients.csv`: leading coefficients for 3 <= r <= 30,
  1 <= a <= 40.
- `data/symbolic_identity.json`: formal algebra check and SymPy version.
- `STATUS.md`: what is proved, imported, checked, and not claimed.
- `sources.md`: primary-source and current-status audit.
- `notes/proof_audit.md`: focused algebra and indexing audit.
- `inputs/manifest.tex`: unchanged supplied selection reference.

**Status:** AI-assisted research draft, not independently refereed or
formally verified. Source searches did not locate a later proof, but do not
establish priority. See `STATUS.md` and `sources.md` for the precise scope.
