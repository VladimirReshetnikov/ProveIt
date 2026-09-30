# Local Minimax Geometry of Uniform Convolution Factors

**Mixed collision strata, boundary-localized Gaussian confounding, and regular variance estimation at positive collisions**

Research article prepared for Vladimir Reshetnikov · 29 September 2026.

## Main result

The model is

    X = Z + sum_i a_i U_i + sqrt(v) G,

where Z has a known bounded distribution, the U_i are independent uniforms on
[-1,1], G is an independent standard Gaussian, the ordered half-lengths belong
to a fixed compact interval, and the capacity M is fixed. Gaussian variance is
known and positive, or unknown in a fixed nondegenerate compact interval bounded
away from zero.

At a reference factorization, let r widths vanish and let the distinct positive
widths have multiplicities m_1,...,m_s. On every sufficiently small fixed
neighborhood, the article proves matching minimax expected-loss rates:

| Target | Known Gaussian variance | Unknown Gaussian variance |
|---|---|---|
| Positive block of multiplicity m_j | n^(-1/(2m_j)) | n^(-1/(2m_j)) |
| Zero block of size r >= 1 | n^(-1/(4r)) | n^(-1/(4r+4)) |
| Gaussian variance | not estimated | n^(-1/(2r+2)) |

The block loss is maximum ordered half-length error. A single full-model
moment estimator adapts to each fixed stratum without knowing the pattern.
The variance remains root-n estimable when r=0, even at positive collisions;
an analytic estimator, its influence polynomial, and asymptotic normality are
proved explicitly.

The new algebraic inputs are a localized shifted-moment inverse theorem and a
nonnegative-coefficient certificate for recovery of the missing first power
sum. Exact matching paths and weighted Gaussian likelihood expansions give
the lower bounds. The all-zero case recovers, rather than newly claims, the
existing global results in ProveIt.

## Contents

- `article.pdf`: 20-page article with proofs, examples, and eight further questions.
- `article.tex`: standalone LaTeX source with embedded bibliography.
- `verify_results.py`: finite symbolic checks and optional likelihood diagnostics.
- `verification_results.json`: recorded output of the full successful run.
- `SOURCE_AUDIT.md`: pinned repository, inspected sources, and novelty boundary.
- `CLAIM_LEDGER.md`: proof locations and validation status.
- `BUILD_VALIDATION.md`: compilation, rendering, and verification record.
- `requirements.txt`: dependency versions used for the supporting script.
- `Makefile`: commands for rebuilding the PDF and rerunning checks.
- `SHA256SUMS.txt`: checksums of the other distributed files.

## Reproduce

Use Python 3.10 or newer and install the dependencies:

```sh
python -m pip install -r requirements.txt
python verify_results.py --output recomputed/exact.json
python verify_results.py --numerics --output recomputed/full.json
```

The recorded run used Python 3.13.5 and passed 186 exact assertions. The optional
numerical integration uses 65-digit arithmetic and the finite interval [-12,12].
It is corroboration, not interval certification. The script rejects Python's
`-O` mode because that mode disables assertions. Without `--output`, it writes
to `verification_results.json` beside the script; using a separate output path
preserves the delivered evidence.

To rebuild the PDF, use a TeX installation with pdfLaTeX, Libertinus, AMS
mathematics, mathtools, microtype, geometry, booktabs, tabularx, enumitem, xurl,
hyperref, and fancyhdr. From this directory run:

```sh
make pdf
```

Equivalently run `pdflatex -interaction=nonstopmode -halt-on-error article.tex`
three times. No BibTeX, external figure files, shell escape, or network access
is needed. Font files are not distributed.

## Scope and status

The central results have full conventional proofs, but have not been
independently refereed or checked in Lean/Rocq. The script does not prove the
universal theorems and does not simulate a minimax risk. It is not a general
implementation of the moment-fitting estimator.

Constants may depend on fixed capacity, cluster gaps, background law, and the
positive variance interval. The article does not prove uniform transition
rates for moving gaps or vanishing variance. It does not claim worldwide
publication priority or resolution of an unrelated named conjecture.

The comparison uses ProveIt commit
`11e1e900114e7c0cfdcd19fe346ddb4f2852dbc5`. No repository files were modified.
