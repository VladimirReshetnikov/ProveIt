# Sharp Two-Mode Extremality for Gaussian Quadratic Fluctuations

**Research manuscript, October 8, 2026.**

The article proves an attained fixed-skewness comparison for normalized centered
Gaussian quadratic forms. If

    Q = sum_i c_i (g_i^2 - 1),  sum_i c_i^2 = 1,  delta = sum_i c_i^3,

and a,b >= 0 satisfy a^2+b^2=1 and a^3-b^3=delta, then

    E f(Q) <= E f(a(g^2-1) - b(h^2-1))

for every C^2 function with convex second derivative and polynomial growth of
its first two derivatives and itself. In particular, this solves the conditioned
absolute-moment maximization problem for every real p >= 3. The article proves
the equality cases, explicit stability estimates, the exact skewness-kurtosis
frontier, and an attained Laplace-transform envelope.

At zero skewness the maximizer is sqrt(2)UV for independent standard normals
U,V. The sharp variance-two fourth-moment bound is 36 rather than the
variance-only bound 60. Zero skewness means the **third trace vanishes**; it does
not mean that the matrix has trace zero or a symmetric spectrum.

## Status and scope

This is an unrefereed research draft prepared with ChatGPT. Its claims have
self-contained mathematical proofs and computational diagnostics, but have not
been independently peer reviewed or Lean certified. The fixed-skewness
strengthening is proposed relative to the primary sources examined; the search
does not establish bibliographic priority. Read `CLAIMS.md` before quoting a
broader assertion.

The nearest primary source examined is Zhekai Pang's September 2026 preprint,
*A Gamma envelope and sharp moment inequalities for Gaussian quadratic forms*,
arXiv:2609.05914v1. Its chord/Poisson method is acknowledged in the article.
The new ingredient here is a sharp asymmetric coefficient enclosure whose
endpoint weights make the envelope an actual feasible two-coordinate form.
The OpenAI repository's Gaussian quadratic-form building blocks supplied the
requested repository inspiration; no major spin-glass assertion is a premise.

## Files

- `article.pdf`: the complete 22-page article.
- `article.tex`, `references.bib`: editable LaTeX and bibliography.
- `code/two_mode.py`: envelope, moment, rigidity, and Chernoff routines.
- `code/verify_exact.py`: symbolic identities and finite integer/rational checks.
- `code/verify_numeric.py`: seeded floating-point diagnostics and Fourier
  quadrature of fractional moments.
- `code/make_figures.py`: regenerates all three figures.
- `code/build_pdf.py`: portable LaTeX/BibTeX build helper.
- `results/`: recorded JSON reports and fractional-moment CSV.
- `figures/`: PDF figures and PNG previews.
- `CLAIMS.md`: precise assertion boundaries and review status.
- `FORMALIZATION.md`: dependency map and proposed formalization stages.
- `provenance.json`: repository snapshot and examined sources.
- `SHA256SUMS`: checksums for the delivered package files.

## Reproduce the calculations

The recorded run used Python 3.13.5. Other Python versions were not tested.
Install the dependencies in a virtual environment:

```sh
python -m venv .venv
# Linux/macOS:
. .venv/bin/activate
# Windows PowerShell instead: .venv\Scripts\Activate.ps1
python -m pip install -r requirements.txt
python code/verify_exact.py
python code/verify_numeric.py
python code/make_figures.py
```

The requirements file records the versions used for this run. Other compatible
versions may work but have not been tested here. Numerical checks use a fixed
seed. Integer and rational identities are exact; floating-point gaps may differ
slightly across platforms. SciPy error estimates are **not interval proofs**.

The recorded exact run passed 97,599 assertions, including 11 symbolic
identities and 385 even-moment comparisons on 77 zero-skewness integer spectra.
The numerical run passed 76,100 assertions using 4,000 random spectra and
80 fractional-moment comparisons. These are finite tests, not certificates of
the all-dimensions theorem.

## Build the PDF

Install a TeX distribution providing pdfLaTeX, BibTeX, and the packages used in
the preamble (`newtx`, AMS packages, `microtype`, `cleveref`, and common graphics
packages). The included PDF requires no local TeX installation to read.

```sh
python code/build_pdf.py
```

The helper runs pdfLaTeX, BibTeX, and two further pdfLaTeX passes. It checks for
unresolved references and overfull boxes, and writes `results/build_report.json`.
It recognizes `bibtex.original` as a fallback for environments with a broken
`bibtex` alternative. Alternatively, on a standard installation:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

`make verify`, `make figures`, and `make pdf` are shortcuts when GNU Make is
available. Rebuilding changes PDF metadata and may change platform-dependent
numerical digits, so delivered checksums are not expected to survive a rebuild.

## Minimal use of the evaluation routines

Run from the package root:

```python
import sys
sys.path.insert(0, "code")
from two_mode import normalize, parameters, kurtosis_frontier, rigidity, chernoff

c, scale, delta = normalize([3, 4, 5, -6])
a, b = parameters(delta)
print("normalized third trace:", delta)       # approximately zero
print("maximum standardized kurtosis:", kurtosis_frontier(delta))  # 9
print("rigidity data:", rigidity(c))
print("right tail, x=5:", chernoff(delta, 5))  # bound, log-rate, optimizer
```

`chernoff(delta, x)` uses Frobenius-norm-one normalization, hence variance two.
A bound can underflow to zero; the logarithmic rate is returned separately.
These floating-point values are evaluations of proved formulas, not certified
upper intervals. Extremely ill-conditioned input may require higher precision.

## Important limitations

The article does not establish rank-one maximization over all skewnesses for
3 <= p < 4, does not treat the conditioned interval 2 < p < 3, and does not
claim pointwise stochastic domination by the two-mode law. Its Chernoff
exponential scale is optimal; its prefactor is not claimed to be the exact
worst-case tail prefactor. The general spectral-distance formula allows zero
padding, which matters for one-sign spectra. The general infinitely divisible
extension has no asserted equality classification.

No files in a remote repository or Library were modified by preparing this
package. No Lean theorem or external mathematical claim was silently imported
as a computational axiom.
