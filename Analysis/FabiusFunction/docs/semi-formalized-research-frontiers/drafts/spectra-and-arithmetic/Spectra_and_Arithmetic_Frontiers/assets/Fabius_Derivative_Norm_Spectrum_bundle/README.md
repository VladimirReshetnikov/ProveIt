# Derivative Norm Spectra and Dual Moment Geometries of the Fabius--Rvachev System

This archived companion bundle preserves the reproducibility code, figures,
and data from the former standalone research report prepared from a recursive
audit of all LaTeX documents under `Analysis/FabiusFunction/docs` in Vladimir
Reshetnikov's `ProveIt` repository, pinned to commit
`0341bbf91cb867f4510bc8431cf59878208de771` (27 August 2026).
The report itself is now incorporated into the consolidated source and PDF two
levels above this directory.

## Main files

- `../../Spectra_and_Arithmetic_Frontiers.tex` -- consolidated LaTeX source.
- `../../Spectra_and_Arithmetic_Frontiers.pdf` -- consolidated rendered report.
- `numerical_experiments.py` -- fully commented reproducibility code.
- `figures/` -- PDF figures used by LaTeX and PNG preview copies.
- `data/` -- CSV tables and a plain-text numerical run summary.
- The former distributed-file checksum ledger is retired and recoverable from
  Git history.

## Live-source / retained-artifact boundary

The current consolidated source has 8,183 lines, 349,076 bytes, and SHA-256
`683a560044772216980b05c4dd26957c6bbfb6c34019cc8d4cae815d9cff8df1`.
It uses `\TwoAdicValuation` for every genuine dyadic valuation.  The retained
consolidated PDF has SHA-256
`2a97dc10398bc4f7d2eaf109c5d28a746355d2e6ddece6e7ee32c5897f487e72`
and predates this notation-only source successor.  No PDF was regenerated:
The former ledger was therefore a mixed byte inventory of current TeX and a
retained PDF checkpoint, not evidence that those two files were synchronized.
It is now retired and recoverable from Git history.

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

From this companion directory, run three passes so that the table of contents
and cross-references settle:

```bash
cd ../..
pdflatex -interaction=nonstopmode -halt-on-error Spectra_and_Arithmetic_Frontiers.tex
pdflatex -interaction=nonstopmode -halt-on-error Spectra_and_Arithmetic_Frontiers.tex
pdflatex -interaction=nonstopmode -halt-on-error Spectra_and_Arithmetic_Frontiers.tex
```

A TeX Live installation containing Libertinus, `amsmath`, `mathtools`, `booktabs`,
`longtable`, `graphicx`, `hyperref`, and `cleveref` is sufficient. If Libertinus is not
installed, the source automatically falls back to Latin Modern.

> **Editorial note (2026-08-28):** the report source (.tex) and compiled PDF listed above were removed from this directory after their content was merged into the volume `Spectra_and_Arithmetic_Frontiers.tex`; their SHA-256 hashes remain in the volume provenance section, and git history archives the files. This directory keeps only figures, data, and scripts.
