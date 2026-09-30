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

- `article.pdf`: 21-page article (20 pages as delivered) with proofs, examples, and eight further questions.
- `article.tex`: standalone LaTeX source with embedded bibliography.
- `verify_results.py`: finite symbolic checks and optional likelihood diagnostics.
- `verification_results.json`: recorded output of the full successful run.
- `SOURCE_AUDIT.md`: pinned repository, inspected sources, and novelty boundary.
- `CLAIM_LEDGER.md`: proof locations and validation status.
- `BUILD_VALIDATION.md`: compilation, rendering, and verification record.
- `requirements.txt`: dependency versions used for the supporting script.
- `Makefile`: commands for rebuilding the PDF and rerunning checks.
- The submitted checksum ledger `SHA256SUMS.txt` was verified in full (10/10) on
  filing (batch 54 of `docs/incoming/`) and not kept; the delivered archive
  remains in the repository history (see `docs/incoming/README.md`, batch 54
  row).

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
to `recomputed/verification_results.json` (editorial amendment below; the
delivered script overwrote the recorded `verification_results.json` beside
it), so the delivered evidence is preserved.

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

## Editorial amendments (ProveIt, 2026-09-29)

This package was filed whole in batch 54 of the repository-level
`docs/incoming/` drop zone (see `docs/incoming/README.md`) and amended in
the editorial pass that followed.

- `article.tex`: an unnumbered environment `ednote` ("Editorial note
  (ProveIt, 2026-09-29)") is defined after the last theorem style, and one
  note follows the proof of Corollary `cor:joint`. Corollary `cor:joint`
  proves, for unknown Gaussian variance and at the level of minimax sampling
  rates `n^(-1/(2 D_U))`, the conjectural local denominator
  `max({m_1,...,m_s} ∪ {2(m_0+1) : m_0 > 0})` of the research question
  "Classify all local strata with unknown variance" in
  `../Gaussian_Confounding_Sharp_Recovery_Uniform_Factors/` (marked
  CONJECTURAL in its `CLAIM_LEDGER.md`; its `m_0` is `r` here); the pairwise
  Hellinger-modulus form is not stated. The known-variance denominator
  `D_K = max{Q, 2r}` is the total-variation denominator of
  `../Sharp_Stability_Strata_Fabius_Rvachev_Deconvolution/`, whose research
  question "The optimal statistical experiment near collisions" is thereby
  answered for the Gaussian-smoothed model only. The article cites neither
  question; its `SOURCE_AUDIT.md` records that the predecessor was read in
  truncated form. The introduction's sentence crediting the open mixed-strata
  question to `../Flat_Boundaries_Sharp_Recovery_Uniform_Factors/` gains a
  `% ed.` comment: that question ("Mixed collision strata at the zero-noise
  boundary") concerns zero Gaussian variance, remains open, and is this
  article's own question on mixed strata without a positive variance floor.
  Notation: the Gaussian-confounding article writes `m` for the capacity,
  `r` for a shift and `M` for its candidate denominator; here `M` is the
  capacity and `r` the number of vanishing half-lengths.
- `article.pdf`: rebuilt with three `pdflatex -interaction=nonstopmode
  -halt-on-error article.tex` passes (MiKTeX pdfTeX): 21 pages (20 as
  delivered; the note adds one), 653,404 bytes; no error, undefined
  reference, rerun request, duplicate destination or overfull box; no Type 3
  font. `BUILD_VALIDATION.md` is the delivered record and still describes the
  20-page build, the overwriting command and the retired ledger.
- `verify_results.py`: the default `--output` is now
  `recomputed/verification_results.json` instead of the recorded file, and
  the JSON is written with LF line endings on every platform (the delivered
  script wrote CRLF on Windows). Changes are marked `# ed.`. The `Makefile`
  targets already wrote to `recomputed/`; they call bare `python`, so use
  `py` or `uv run` where that does not resolve.
- Rerun on a copy (2026-09-29), `uv run --no-project --python 3.13.5 --with
  sympy==1.14.0 --with mpmath==1.3.0 python verify_results.py --numerics`
  (about 70 seconds): 186 exact assertions and four likelihood diagnostics;
  the output is byte-identical to the recorded `verification_results.json`.
- Lean (not cited by the article): `Fabius.sinhDivLogCoefficient_eq_bernoulli_formula`
  and `Fabius.centeredRvachevEvenCumulant_eq_bernoulliMersenne_formula`
  (`Analysis/FabiusFunction/Lean/FabiusFunction/SinhDivBernoulliLog.lean`,
  lines 259 and 277) prove the uniform cumulant formula
  `c_k = 2^(2k) B_(2k)/(2k)` (as the coefficient of `X^k` in
  `log(sinh(√X)/√X)`, times `(2k)!`) and the up-law cumulants
  `c_k/(2^(2k) − 1)` that the article uses.
- `SHA256SUMS.txt`: see Contents (retired on filing).
