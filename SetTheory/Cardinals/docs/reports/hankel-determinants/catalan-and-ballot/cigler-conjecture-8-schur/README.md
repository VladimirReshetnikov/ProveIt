# Rectangular Schur Polynomials and Cigler's Conjecture 8

**Result:** A complete mathematical proof draft of Conjecture 8 in
Johann Cigler, arXiv:2111.14492v3, Section 4, printed pages 16–17.
The article proves every assertion of that conjecture, including the
numerator-polynomial degree and reciprocity assertions.

**Research date:** 20 September 2026.

## Main identity

For

    b_m(t) = sum_r binom(floor(m/2),r) binom(ceil(m/2),r) t^r,

we prove, for all integers k,n >= 0,

    det(b_{2k+i+j}(t))_{0 <= i,j < n}
      = t^floor(n^2/4) s_(n^k)(1,...,1,t,...,t),

with k copies of each value in the Schur polynomial. Empty determinants
and the empty Schur polynomial equal 1. The normalized determinant is
therefore a polynomial, including at t=0 where direct division of
specialized determinant values would be invalid.

The proof converts a Laurent-polynomial Gram determinant to a Toeplitz
determinant. The subsequent tableau formula proves coefficient positivity
and symmetry. Restricting a Schur module to SL(2) proves unimodality.
A confluent alternant gives the explicit numerator polynomials.

## Relation to the supplied manifest

The related entry is **Product formulas for ballot-polynomial Hankel
determinants**, cataloguing Cigler's **Conjectures 13–15 in Section 5**.
This package instead resolves **Conjecture 8 in Section 4**, for a different
moment family. No result from the manifest is assumed in the proof.
The original supplied manifest is retained unchanged in inputs/manifest.tex.

## Contents

- `article.pdf`: the typeset article.
- `article.tex`: complete LaTeX source, with its bibliography included.
- `code/verify.py`: standard-library exact verifier for five formulations.
- `code/verify_consequences.py`: additional edge, recurrence, and symbolic
  asymptotic-constant checks.
- `results/verification.json`: primary verification summary.
- `results/polynomials.json`: all 77 normalized coefficient lists, in
  **ascending powers of t**.
- `results/numerator_blocks.json`: selected numerator blocks, indexed by j
  and then by ascending powers of t.
- `results/consequences.json`: supplementary verification summary.
- `results/run.txt`: recorded console output of the primary verifier.
- `STATUS.md`: proof status, imported facts, and limitations.
- `sources.md`: source/version audit and literature-search limitations.
- `build.sh`: PDF build command.

## Reproduce the calculations

Python 3.10 or later is sufficient. There are no third-party Python
requirements, no network calls, and no floating-point computations.

```sh
python3 code/verify.py
python3 code/verify_consequences.py
```

The default primary grid is 0 <= k <= 6 and 0 <= n <= 10: 77 parameter
pairs, 231 determinant-to-partition comparisons, 66 numerator
reconstructions, and 35 independent signed-permutation determinant audits.
The recorded run had zero disagreements. The three determinant formulas
share a Bareiss implementation; the separate signed-permutation audit
checks that engine without using elimination.

The supplementary run verifies 66 first post-stable coefficients, six
symbolic leading coefficients controlling the asymptotic deficit, and nine
recurrence windows using raw Hankel computations (up to order 14).

Optional larger primary grid:

```sh
python3 code/verify.py --max-k 7 --max-n 12 --output-dir results/larger
```

The partition enumeration is finite but not intended as a high-performance
method for very large rectangles. Every exact division checks its remainder
and integrality; discrepancies raise exceptions rather than being ignored.
These calculations support reproducibility and are not substitutes for the
all-parameter mathematical proof.

## Rebuild the article

A LaTeX installation containing pdfLaTeX and the packages named in the
preamble is required. A normal TeX Live installation suffices.

```sh
sh build.sh
```

The script performs three passes and places `article.pdf` in this folder.
Build intermediates go to `_build/`. No font files or third-party source
papers are distributed in this archive.

## Additional results

The article also proves a positive rectangular-partition sum with squared
Weyl dimensions; stable edge coefficients; the first correction beyond that
stable edge; a product at t=1; coefficientwise monotonicity in n; the exact
generic recurrence over Q(t); and fixed-t asymptotics in the regimes
0<t<1, t=1, and t>1.

## Research status

The proof is an unrefereed AI-assisted research draft, not a proof-assistant
formalization. It imports standard Schur identities and the classical
Schur-module character theorem, with explicit references. A targeted public
search did not locate an earlier resolution of the selected conjecture.
This does not establish absolute priority. See `STATUS.md` and `sources.md`.
