# Complementary depth, classical ladders, and exact shuffle ranks

A research contribution for **ProveIt / Analysis / Polylogarithms**, prepared
9 October 2026 for Vladimir Reshetnikov.

The full argument is in `article.pdf` (18 pages) and its editable source
`article.tex`. This package does not overwrite or commit to the repository.

## Main results

The article proves the three weight-four Gaussian triple formulas for
`Im Li_(2,1,1)(i,1,1)`, `Im Li_(1,2,1)(i,1,1)`, and
`Im Li_(1,1,2)(i,1,1)` printed as numerical candidates in Chapter 4 of the
inspected manuscript. It proves an all-weight classical reduction for
`Li_({1}^a,2,{1}^b)(z,1,...)`, a short terminal-2 ladder, and a two-zero
height-one reduction to double polylogarithms. All have explicit Gaussian
and Eisenstein specializations.

More generally, a one-variable MPL of weight w and depth d is reduced to a
finite rational combination of

    L^j Li_A(q,1,...) zeta(B),   q = 1/(1-z),   L = log(q),
    depth(A) + depth(B) <= w-d.

This bound treats L as a coefficient and changes the argument family.
It is not a claim about reduction inside an unchanged cyclotomic basket.
The functional identities use principal branches on C minus [0,infinity).

A separate theorem determines the formal binary shuffle-product rank at
every weight and depth. It explains rank seven on ten weight-six triple
coordinates, with the three formal Lyndon representatives (4,1,1), (3,2,1),
and (3,1,2). It is not a numerical independence theorem.

A correction to the mixed-color antisymmetry discussion is proved by the
explicit nonzero diagonal difference

    Li_(1,1)(i,-1) - Li_(1,1)(-1,i)
      = pi^2/24 - log(2)^2/4 + i*(Catalan - pi*log(2)/2).

The manuscript's S4 formula remains unproved in this contribution. A dual
witness shows that its left side is outside one precisely specified
134-row finite depth-two law system. This is a statement about that row
space, not a disproof of the conjecture.

## Status and originality

These are analytic proofs and exact finite computations, not Lean or other
proof-assistant verification. The draft is unrefereed. Harmonic-polylogarithm
transformations, Nielsen functions, and the polynomial Lyndon description
of the shuffle algebra are established mathematics; no global priority
claim is made for that machinery. The contribution is its explicit,
branch-controlled application to the manuscript, the formulas and
specializations, the certificates, and the identified correction.

Numerical residuals are diagnostics, not proofs of transcendental equality.
Rational intervals enclose the values using the already proved identities;
overlap of two intervals is not offered as a proof of equality.

## Reproduce

Python 3.10 or later is required. The recorded run used Python 3.13.5,
SymPy 1.14.0 and mpmath 1.3.0. Install the two Python dependencies with
`python -m pip install -r requirements.txt`.

From this directory:

```sh
make test
make pdf
```

Or run each component separately:

```sh
python code/check_exact.py
python code/check_numerical.py
python code/certify_gaussian.py
python code/audit_s4_rows.py
python code/replay_certificates.py
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The PDF build needs latexmk and a standard TeX Live distribution including
amsmath, amsthm, mathtools, lmodern, microtype, booktabs, enumitem, hyperref,
and fancyhdr. `make clean` removes TeX auxiliary files, not the PDF.

`code/replay_certificates.py` only uses the Python standard library and
replays the stored exact word, matrix, and enclosure-width certificates.
It does not regenerate the analytic identities or certify their endpoint
estimates independently of the article. The other scripts regenerate the
reports and data.

## Recorded verification

The finite exact checks cover 511 trailing-zero re-expansions, 66 one-zero
formulas through weight twelve, ten two-zero formulas through weight twelve,
1023 Lyndon triangularity checks, the 7-by-10 triple matrix, and all three
Gaussian substitutions. The catalogue contains 142 high-depth entries
through weight eight, with 5763 exact nonzero terms.

Independent quadrature checks passed in 153 cases at 75 decimal digits;
the largest residual was 1.37724278367e-73. Exact-rational Gaussian interval
calculations give enclosure widths below 1e-90 for all six real/imaginary
components of the three triples. See `verification.log` and the JSON reports.

## Contents

| Path | Purpose |
|---|---|
| `article.tex`, `article.pdf` | Full proofs, qualifications, references, and further questions |
| `code/polylog_words.py` | Exact word transport, normalization, explicit formulas, Lyndon operations |
| `code/check_exact.py` | Independent exact comparisons and catalogue generation |
| `code/check_numerical.py` | Original-side quadrature versus transformed nested series |
| `code/certify_gaussian.py` | Exact-rational interval arithmetic and tail estimates |
| `code/audit_s4_rows.py` | Finite law matrix and exact dual obstruction |
| `code/replay_certificates.py` | Standard-library certificate replay |
| `certificates/` | Exact reductions, matrices, dual witness, rational endpoints and reports |
| `tables/shuffle_ranks.csv` | Formal dimensions and product ranks through weight ten |
| `integration/` | Proposed manuscript insert and specific editorial changes |
| `SOURCE-PROVENANCE.json` | Repository snapshot and primary references |
| `MANIFEST.sha256` | Hashes of delivered files |

## Integration

Review `integration/EDITORIAL-NOTES.md` before changing the manuscript.
A suitable additive location is
`Analysis/Polylogarithms/docs/complementary-depth/`.
The insert uses the manuscript's existing `\Li` command and theorem
environments and avoids modifying their definitions. It links the triple
candidate proof upgrade to this companion article; other numerical
candidates are not silently upgraded.
