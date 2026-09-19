# Rational exponents, non-D-finite coefficient counts

**Main result.** Define G(2j+1)=2^j and G(2j+2)=3^j for j>=0, and let
nu(N) count the coefficients equal to one in the polynomial

    P_N(x) = product(i=1..N) (1 + x^G(i)).

The generating function of G is rational, but the generating function of
nu is not D-finite and has a natural boundary. If a(n)=nu(2n), then

    a(0)=1, a(1)=2,
    a(n)=2^floor((n+1)*(1-log(2)/log(3)))  for n>=2.

The article proves the result without assuming anything about the
algebraicity or transcendence of the exponential growth constant.

The general family G_b(2j+1)=2^j, G_b(2j+2)=b^j, b>=3, has a rational
coefficient-count generating function exactly when b is a power of two.
For every other b, that count series is not D-finite.

## The problem being answered

Richard Stanley, “A conjectured rational generating function,”
MathOverflow question 431075, September 23, 2022:
https://mathoverflow.net/questions/431075/a-conjectured-rational-generating-function

The question displayed no posted answers when checked on September 19,
2026. This package answers the universal rationality part negatively; it
does not classify every possible exponent recurrence.

**Scope caveat:** the example is positive and tends to infinity but is not
monotone. Monotonicity is not a hypothesis of the cited question. A variant
with an additional monotonicity requirement is not settled here.

**Research status:** complete written proofs and exact computational checks
are provided. The work is unrefereed, priority is unverified, and there is
no formal proof-assistant certification. Nothing has been posted or
submitted to MathOverflow or OEIS on the user's behalf.

## Contents

- `article.tex` and `article.pdf`: the comprehensive 17-page research article.
- `short_solution.md`: a concise standalone proof of the counterexample.
- `verify.py`: exact-integer Python implementation and tests, standard library only.
- `verification.json`: machine-readable results from an actual full test run.
- `verification_run.txt`: the corresponding console output.
- `data/binary_ternary_counts.csv`: G(N) and nu(N), N=0..400 (G(0) is a placeholder 0).
- `data/even_counts_b3.txt`: a(n), n=0..1000, in OEIS-style two-column format.
- `data/base_comparison.csv`: even-prefix counts for b=3,4,5,8,9,16, n=0..100.
- `source_status.md`: source provenance and limitations of the status search.
- `Makefile`: verification and PDF build targets.

No existing OEIS identifier is asserted for the generated data.

## Reproduce the computations

Python 3.10 or later is required; the supplied run used Python 3.13.5.
No third-party Python packages or network access are required.

```sh
python3 verify.py
```

A smaller test run is available as `python3 verify.py --quick`. Full mode
performs exact polynomial multiplication through N=28 (largest polynomial
degree 2,407,867), 1,210 independent interval-sweep grid cases, 150 seeded
random sweep cases, and further exact checks of every displayed counting
identity. The full run is preferable and was executed for this package.

Import the implementation directly:

```python
from verify import coefficient_count, ones_formula, iter_even_counts

assert coefficient_count(3, 20) == 16
assert ones_formula(3, 10, 10) == 16
assert list(iter_even_counts(3, 10)) == [1, 2, 2, 2, 2, 4, 4, 4, 8, 8, 16]
```

`iter_even_counts` streams the sequence with one exact threshold comparison
per new term. It avoids floating-point logarithms entirely.

## Build the article

A standard TeX Live installation with pdfLaTeX, NewTX, AMS packages,
microtype, tcolorbox, listings, aliascnt, hyperref and cleveref is sufficient.
The bibliography is embedded in `article.tex`; BibTeX is not needed.

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively, run `make all`. Font binaries and third-party papers are
not redistributed. Sources are cited in the article.

## What computation does and does not certify

The dense multiplication and interval-event sweep are independent of the
closed-form threshold formula. They check implementation and indexing.
The universal nonrationality, non-P-recursiveness, natural-boundary theorem,
and base classification are consequences of the proofs, not of the finite
test ranges. Finite tests alone could not establish those conclusions.
