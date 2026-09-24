# Esthetic Numbers, Folded Paths, and Algebraic Diagonals

**Research note dated 19 September 2026.**

The principal target is the diagonal conjecture in OEIS A377000:

    T(q,q-2) = A182555(q-2), q >= 3,

where T(q,k) counts base-q positive integers of length k whose adjacent
digits differ by one. The article supplies an exact proof, proves the
other two conjectures as stated in the retrieved entry, and derives
formulas for every fixed-offset diagonal q=k+d.

## Read first

- `article.pdf`: the complete 18-page article, including English proofs,
  source attribution, boundary cases, exact verification, and a draft
  OEIS update.
- `article.tex`: editable LaTeX source; no external figures or bibliography
  files are required.
- `sources.md`: the source and status audit.

The classical spectral enumeration and the differential-composition model
are attributed to the original authors. In particular, recurrence
existence alone already follows from the known spectral formula. The
research claim is a self-contained resolution and extension of the
retrieved conjectures, not a certification of worldwide priority. There
is no claim of peer review, formal proof-assistant verification, or an
OEIS submission.

## Main mathematical results

1. T(q,k) is half the number of k-step walks on the path with q vertices,
   for k>=1. A reflection-orbit bijection handles the no-leading-zero rule.
2. For even q, folding the path produces the graph of meaningful
   differential compositions on R^(q-1).
3. Every row has the explicit minimal Chebyshev recurrence proved in
   Theorem 4.1, including the zero-eigenvalue exception for q=1 mod 4.
4. T(k+2,k)=A182555(k) and T(k,k)=A206603(k), on the valid domains.
5. Every fixed-offset diagonal generating function is rational minus
   sqrt(1-4z^2)/(2(1-2z)^2). It is therefore algebraic of degree exactly two,
   and any two such generating functions differ by a rational function.
6. For q=k-c, the eventual correction is an explicit polynomial P_c(k)
   of degree floor((c-1)/2), valid at k>=max(c+2,2c-1). The paper gives all
   earlier exceptional terms and proves the threshold sharp for c>=4.

## Reproduce the exact checks

Python 3.10 or later is sufficient for the main verifier. It has **no
third-party dependencies** and uses no network access.

```sh
python3 verify.py
```

This regenerates the CSV and JSON data, including
`verification/results.json`. The archived run used Python 3.13.5 and
passed 75,381 exact equalities or nonsingularity checks. The exhaustive
part also enumerated all 131,070 sign words of lengths 1 through 16.
Elapsed time is recorded for context and will vary on another machine.

The verifier compares several independently implemented descriptions:
digit-endpoint dynamic programming, unrestricted path walks, folded-path
walks, the differential-operation adjacency graph, brute-force walk
ranges, Catalan expansions of the named generating functions, sorted
binomial weights for addition triangles, and exact Hankel determinants.
Finite verification is not a substitute for the universal proofs.

Useful functions can be imported without running the test suite:

```python
from verify import digit_row, reflection_formula, minimal_polynomial

# Index zero is a dummy entry, NOT an empty-word count.
row = digit_row(q=10, maximum_length=100)
assert row[4] == 61
assert reflection_formula(10, 4) == 61

# Polynomial coefficients are in ASCENDING powers of x.
assert minimal_polynomial(6) == [1, -2, -1, 1]
```

### Optional symbolic verification

The optional program uses SymPy. The tested version is pinned in
`requirements-symbolic.txt`.

```sh
python3 -m pip install -r requirements-symbolic.txt
python3 symbolic_verify.py
```

It computes exact matrix resolvents for 2<=q<=14, checks the row formula
and every reduced denominator, and checks three scalar rational identities.
Its output is `verification/symbolic_results.json`.

### Data conventions

`data/rows.csv` records q=2..40 and k=1..100.
`data/diagonals.csv` records d=-12..12 and every valid k<=200.
`data/minimal_polynomials.json` records bases q=2..100, in ascending
coefficient order.
`data/hankel_determinants.json` records the nonzero determinants of
[T(q,1+i+j)] at the proved minimal order for q=2..40.

The article extends the row count to q/2 at k=0 only for formal generating
functions. This is NOT a count of empty digit strings. `digit_row` instead
uses a dummy zero in slot 0, and the verifier never conflates these two
conventions.

## Build the PDF

A TeX distribution with pdfLaTeX and the packages named in the preamble is
required (including newtx, amsmath, amsthm, mathtools, microtype, tcolorbox,
hyperref, fancyhdr, and titlesec).

```sh
make pdf
# Equivalent:
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

`make verify` runs the standard-library suite; `make symbolic` runs the
optional symbolic suite. `make clean` removes TeX intermediates, not the
article PDF, sources, or verification results.

No external papers, font files, checksum files, or untested Lean code are
included in this archive.
