# Derivative Norm Spectra and Dual Moment Geometries of the Fabius--Rvachev System

This bundle accompanies the research report prepared from a recursive audit of all
LaTeX documents under `Analysis/FabiusFunction/docs` in Vladimir Reshetnikov's
`ProveIt` repository, pinned to commit
`0341bbf91cb867f4510bc8431cf59878208de771` (27 August 2026).

## Main files

- `Fabius_Derivative_Norm_Spectrum.tex` -- complete LaTeX source.
- `Fabius_Derivative_Norm_Spectrum.pdf` -- rendered 26-page report.
- `numerical_experiments.py` -- fully commented reproducibility code.
- `figures/` -- PDF figures used by LaTeX and PNG preview copies.
- `data/` -- CSV tables and a plain-text numerical run summary.
- `SHA256SUMS.txt` -- checksums for every distributed file except the checksum file itself.

## Central new deductions (relative to the pinned repository corpus)

The report proves an exact equimeasurability law for every derivative of Rvachev's
up-function, hence exact scaling in every rearrangement-invariant norm. It derives an
inverse-Fabius beta transform and an Euler--Gamma differential operator whose coefficients
are Bell polynomials in Euler/zeta cumulants, with finite-parameter corrections governed by
Bernoulli polynomials. It then combines this calculus with the periodic inverse endpoint
expansion to obtain large-p norm laws and phase tomography. On the Fourier side, the same
norm ladder produces a shifted Stieltjes--Wigert moment problem with an explicit sinc-square
representing measure, q-binomial orthogonal polynomials, closed Hankel determinants, and a
nonclassical q-Pearson equation.

"New" is a corpus-relative novelty label after formula- and terminology-level collision
checking; the report does not claim universal publication priority.

## Reproduce the numerical experiments

The script requires Python 3 with NumPy, SciPy, SymPy, and Matplotlib:

```bash
python numerical_experiments.py --output-dir .
```

The default run uses `2**19` samples and 55 dyadic sinc factors. It regenerates every file in
`figures/` and `data/`. The calculations are checks only; the report gives analytic proofs of
the central identities.

## Compile the report

Run twice so that the table of contents and cross-references settle:

```bash
pdflatex -interaction=nonstopmode -halt-on-error Fabius_Derivative_Norm_Spectrum.tex
pdflatex -interaction=nonstopmode -halt-on-error Fabius_Derivative_Norm_Spectrum.tex
```

A TeX Live installation containing Libertinus, `amsmath`, `mathtools`, `booktabs`,
`longtable`, `graphicx`, `hyperref`, and `cleveref` is sufficient. If Libertinus is not
installed, the source automatically falls back to Latin Modern.
