# Gaussian Dust and Christoffel Recovery in Infinite Uniform Convolutions

**Exact non-estimability, a complete compact-class criterion, and geometric moment formulas beyond finite capacity**  
Research manuscript prepared for Vladimir Reshetnikov, 29 September 2026.

## Read

`article.pdf` is the compiled article. `article.tex` is a self-contained source,
including its bibliography and numerical table. No external figures, source
papers, bibliography processor, shell escape, or network access are needed.

The observation model is a known centered smooth compactly supported random
background plus an independent Gaussian and a sorted square-summable sequence
of independent centered uniform factors. The total latent variance is bounded
by a fixed V > 0. Gaussian variance is denoted by s; total latent variance by v.

## Main results

- At every finite sample size, the exact minimax risks for Gaussian variance
  over the unrestricted class are V/2 in absolute error and V^2/4 in squared
  error. The constant estimator V/2 attains both. A local version is also proved.
- On a compact subclass, uniform consistency is equivalent to uniformly
  vanishing squared-scale tails. One estimator remains pointwise consistent
  on the entire class, despite the constant global minimax risk.
- A variance-weighted spectral measure gives positive finite-cumulant upper
  certificates. Christoffel minimization has bias at most one third of the
  squared-scale tail after deleting d factors.
- For squared scales C r^j, j >= 0, the exact degree-d bias is
  C (1-r) r^d / [3 (1-r^(d+1))^2]. The dyadic up-spectrum is C = r = 1/4.
- A rank-independent total-variation expansion includes explicit sixth- and
  eighth-derivative remainder bounds. Coefficient-constrained regularization
  supplies deterministic noise bounds and statistical upper rates under
  two-sided polynomial or geometric envelopes.

Ten further research questions address sharp rates, weaker envelopes, constrained
moment feasibility, computation, perturbations, higher expansions, unsmoothed
observations, unknown backgrounds, multivariate models, and formalization.

## Attribution and claim boundary

Billey--Swanson's DUSTPAN identifiability and compactification are existing
results, not claimed discoveries. Christoffel variational formulas and Cauchy
determinants are classical. ProveIt already contains Christoffel reconstruction
of the physical up-density; the measure in this article is different and
encodes convolution factors. See `SOURCE_AUDIT.md` and `CLAIM_LEDGER.md`.

The article gives conventional proofs for the stated model. It has not been
independently refereed or verified in Lean/Rocq. Worldwide priority has not been
established. The envelope rates are upper bounds, not proved minimax rates.
No repository files were modified.

## Reproduce the checks

Python 3.10 or newer is recommended. Install the versions in `requirements.txt`,
then run from any directory:

```sh
python verify_results.py
```

The program checks exact rational identities and writes its outputs to
`recomputed/` unless `--output-dir` is given (editorial amendment below; the
delivered script rewrote `artifacts/` in place). The recorded outputs are in
`artifacts/`; `artifacts/verification_summary.txt` is a hand-written summary,
not program output.
The delivered run passed 4,619 exact assertions and three high-precision
Fourier diagnostics. The Fourier diagnostics do not compute total variation,
and finite checks do not replace the universal proofs. Validation uses explicit
exceptions, so `python -O` does not disable it.

## Build the PDF

Use a TeX distribution with pdfLaTeX and the packages named in `article.tex`,
including Libertinus, AMS mathematics, microtype, booktabs, tabularx, enumitem,
xurl, hyperref, cleveref, and fancyhdr.

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively run `make pdf` and `make check`.

## Archive contents

`article.tex`, `article.pdf`, `verify_results.py`, `requirements.txt`, `Makefile`,
this README, the source audit, claim ledger, build-validation record, and exact
and diagnostic data in `artifacts/`. TeX auxiliary files and font files are not
included. The submitted checksum ledger `SHA256SUMS.txt` was verified in full (15/15) on
filing (batch 54 of `docs/incoming/`) and not kept; the delivered archive
remains in the repository history (see `docs/incoming/README.md`, batch 54
row).

## Editorial amendments (ProveIt, 2026-09-29)

This package was filed whole in batch 54 of the repository-level
`docs/incoming/` drop zone (see `docs/incoming/README.md`) and amended in
the editorial pass that followed.

- `article.tex`: an unnumbered environment `ednote` ("Editorial note
  (ProveIt, 2026-09-29)") is defined after the last theorem style, and one
  note follows the paragraph distinguishing the up-density Christoffel
  reconstruction (Section 1.2). Theorems `thm:minimax` and `thm:criterion`
  answer, for the Gaussian-variance functional, the research question
  "Gaussian components and square-summable spectra" of
  `../Recovering_Uniform_Factors_Fabius_Rvachev/`: without a tail
  restriction the exact minimax risk is `V/2` (absolute error) and `V²/4`
  (squared error) at every sample size, and a compact class admits
  uniformly consistent estimation exactly when its squared-scale tails
  vanish uniformly. They bear on the research questions "Unbounded capacity
  and tail-controlled infinite products" of
  `../Sharp_Stability_Strata_Fabius_Rvachev_Deconvolution/` and "Growing
  capacity and the infinite-factor transition" of
  `../Gaussian_Confounding_Sharp_Recovery_Uniform_Factors/` only for the
  variance; the recovery modulus of the scales is not treated. The article
  cites those reports but not those questions (its `SOURCE_AUDIT.md`
  records a partial reading of the group README). The note also points to
  the fixed-capacity local rates of `../Local_Minimax_Geometry_Uniform_Factors/`,
  which writes `v` for the Gaussian variance (`s` here) and `M` for the
  capacity (a coefficient-ball radius here). Changes are marked `% ed.`.
- `article.pdf`: rebuilt with three `pdflatex -interaction=nonstopmode
  -halt-on-error article.tex` passes (MiKTeX pdfTeX), US Letter as
  delivered: 23 pages (22 as delivered; the note adds one), 685,058 bytes;
  no error, undefined reference, rerun request, duplicate destination or
  overfull box; no Type 3 font. `BUILD_VALIDATION.md` is the delivered
  record and still describes the 22-page, 611,147-byte build and the
  retired ledger.
- `artifacts/*.csv`: the three delivered CSV files had CRLF line endings
  (Python's `csv` module) and were normalized to LF on filing.
- `verify_results.py`: a new option `--output-dir` (default `recomputed/`)
  replaces the delivered in-place rewrite of `artifacts/`; JSON files are
  written with LF line endings and the CSV writers use
  `lineterminator="\n"`, so reruns reproduce the filed LF files. Changes are
  marked `# ed.`. The `Makefile` target `check` calls bare `python`; use
  `py` or `uv run` where that does not resolve.
- Rerun on a copy (2026-09-29), `uv run --no-project --python 3.13.5 --with
  sympy==1.14.0 --with mpmath==1.3.0 python verify_results.py`: 4,619 exact
  checks and three Fourier diagnostics passed; all five program outputs are
  byte-identical to the filed files in `artifacts/`.
- Lean (not cited by the article): the uniform cumulant formula
  `γ_(2k) = 2^(2k) B_(2k)/(2k)` is `Fabius.sinhDivLogCoefficient_eq_bernoulli_formula`
  (`Analysis/FabiusFunction/Lean/FabiusFunction/SinhDivBernoulliLog.lean`,
  line 259, as the coefficient of `X^k` in `log(sinh(√X)/√X)`, times
  `(2k)!`), and the Rvachev-background variance is the first case of
  `Fabius.centeredRvachevEvenCumulant_eq_bernoulliMersenne_formula` (line
  277). The Lean tree has no Christoffel-function reconstruction
  (`FabiusLegendreHankelDeterminant.lean` disclaims it).
