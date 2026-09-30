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

The program checks exact rational identities and regenerates `artifacts/`.
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
this README, the source audit, claim ledger, build-validation record, exact
and diagnostic data in `artifacts/`, and SHA-256 checksums. TeX auxiliary files
and font files are not included.
