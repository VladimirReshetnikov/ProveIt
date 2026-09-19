# Ballot-polynomial Hankel determinants

**A self-contained proof of the statements labeled Conjectures 13–15 in
Johann Cigler, arXiv:2111.14492v3, Section 5, with stronger coefficient results.**

Prepared for Vladimir Reshetnikov, 19 September 2026.

Start with `article.pdf`. Its editable source is `article.tex`.

## What is proved

For the ballot moments

    a_m(t) = sum_h (binom(m,h) - binom(m,h-1)) t^h,

normalize the shift-k, size-n Hankel determinant by `t^(n(n-1)/2)`.
An explicit coefficient product proves its sign and exact support, and
positivity of every coefficient of its residual polynomial for `n >= 1`.
The same products give the conjectured generating-function denominators,
exact numerator degrees, and reciprocal numerator identities. The report
also proves strict log-concavity of the residual coefficients and gives
their explicit leading asymptotics and limiting binomial profile.

The proof has no computational hypotheses. The tests below supplement it;
they do not establish the unbounded statements by finite checking.

## Status and provenance

The target is Conjectures 13, 14, and 15 **in Section 5**, not the other
families of conjectures elsewhere in Cigler's paper. The cited version was
revised on 30 December 2021. A targeted search during preparation did not
locate a later proof of these exact statements. This is not an exhaustive
priority search, and the report makes no certification of novelty. The
argument has not undergone external peer review or Lean formalization.
See `SOURCES.md` and the article's introduction.

## Contents

- `article.tex`, `article.pdf`: complete article and proofs.
- `code/hankel.py`: exact, standard-library implementation.
- `code/verify.py`: independent numerical determinant and rational-identity tests.
- `code/verify_symbolic.py`: symbolic determinant checks and data generation.
- `data/verification.json`, `data/verification.txt`: results of the exact test suite.
- `data/symbolic_verification.json`: results of the separate symbolic suite.
- `data/numerators.json`: exact numerator/denominator polynomials for `1 <= k <= 10`.
- `data/rho_coefficients.csv`: residual coefficients for `1 <= k <= 12`, `1 <= n <= 20`.
- `build.sh`, `build.ps1`: PDF build conveniences.
- `requirements.txt`: pinned optional symbolic-test dependency.
- `SHA256SUMS.txt`: checksums of the packaged files other than the checksum file itself.

## Run the tests

From this directory, using Python 3.9 or later:

```text
python code/verify.py
python -m pip install -r requirements.txt
python code/verify_symbolic.py
```

The first command requires no third-party packages. It performs **32,666
exact checks**, including 1,292 shifted determinants computed independently
from the defining moments, 91 unshifted determinants, and tests with zero
and negative weights. Fraction-free Bareiss elimination is used for direct
determinants. No floating-point assertions occur.

The second suite performs 24 symbolic bivariate determinant checks, 135
symbolic generating-function tail checks, and ten full symbolic numerator
reciprocity checks. It regenerates the polynomial and coefficient data.
The saved run used Python 3.13.5 and SymPy 1.14.0; elapsed times may differ.

All test failures raise an exception. The scripts print JSON and rewrite
the corresponding files under `data/` on success. Timing metadata can
change on reruns, so rerunning a test changes its checksum.

## Build the article

With `pdflatex` and the ordinary packages from TeX Live or MiKTeX:

```text
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively run `./build.sh` or, in PowerShell, `./build.ps1`.
The source contains its bibliography. No BibTeX step, downloaded source
paper, image, or separate font file is required.

## Use the implementation

From a Python process whose import path includes `code/`:

```python
from hankel import delta, direct_hankel, rho_coefficients_fast, numerator

assert rho_coefficients_fast(4, 2) == [2, 8, 10]  # ascending powers of t
assert delta(4, 2, t=1) == 20
assert direct_hankel(4, 2, t=1) == 20
assert numerator(4, t=1) == [1, 5, 10, 10, 5, 1]
```

`delta(k,n,t,u)` also supports the homogeneous horizontal-step weight `u`.
For `n < 0`, it returns the canonical exponential-polynomial continuation,
not an ordinary determinant. This continuation requires `t != 0`.
For `n >= 0`, the normalized determinant is a polynomial and is evaluated
at `t = 0` without numerical division by zero.

The entries `[i,j,c]` in `numerators.json` represent `c*x**i*t**j`.
Coefficient lists in the Python API and the CSV use **ascending powers**.
In the article, the auxiliary sequence `b_j` is ordered the other way:
`rho_k(n,t) = sum_j b_j*t**(floor(k/2)-j)`.

## The proof in outline

The tridiagonal path operator produces orthogonal polynomials
`P_m = U_m - u*U_(m-1)`. A block determinant reduces the size-n Hankel
determinant to a size-k coefficient determinant. The two-term connection
collapses the column expansion to a shifted prefix followed by an
unshifted suffix: all other terms have duplicate columns. Parity then
leaves only `floor(k/2)+1` minors. Their two parity blocks are Vandermonde
determinants in quadratic node coordinates.

The explicit products are positive integer-valued polynomials on each
parity class of n. Their adjacent ratios prove strict log-concavity, and
their leading terms determine the generating-function denominators. A
negative-index gap determines the exact numerator degrees. Reflection of
the nodes proves the reciprocal identities.

Strict log-concavity is **not** being inferred from real-rootedness:
`rho_4(2,t) = 2 + 8*t + 10*t^2` has discriminant `-16`.
