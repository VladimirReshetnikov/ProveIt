# Integral, Transform, and Fractional-Calculus Frontiers for the Fabius-Rvachev System

> **Archived companion bundle.** The former standalone manuscript is now
> consolidated in `../../Integration_and_Transform_Frontiers.tex`, with the
> rendered report at `../../Integration_and_Transform_Frontiers.pdf`. This
> directory retains its supporting computations and figures.

This archive contains the deterministic Python program used for exact
arithmetic and independent numerical checks of the former standalone report.

## Contents

- `../../Integration_and_Transform_Frontiers.tex` - current consolidated manuscript.
- `../../Integration_and_Transform_Frontiers.pdf` - compiled consolidated report.
- `numerical_experiments.py` - commented exact/numerical verification program.
- `experiments_summary.txt` - exact moments/Jacobi coefficients and all residuals.
- `jacobi_coefficients.tex` - generated exact coefficient table included by the manuscript.
- `up_reconstruction.png` - fixed-point reconstruction diagnostic.
- `jacobi_coefficients.png` - exact Jacobi-coefficient trend.
- `power_quantile_ratio.png` - nonlinear power-integral asymptotic diagnostic.
- `requirements.txt` - Python package versions used for the supplied outputs.

## Principal new results developed in the report

The report distinguishes imported background, newly proved deductions,
conditional statements, and conjectures. Its main corpus-relative additions
include:

1. A survival-kernel calculus giving arbitrary-weight and partial integrals of
   the positive half of Rvachev's up-function and of the bounded Fabius
   function.
2. An entire Newton series for generalized Fabius moments, including negative
   and fractional powers, and a three-function Mellin-transform dictionary.
3. Layer-cake antiderivatives and Laplace/Fourier/Mellin transforms of the
   inverse Fabius function.
4. Riemann-Liouville and Caputo formulae, fractional refinement equations, and
   an incomplete-beta master theorem for fractional antiderivatives of
   `x^p F(x)` and `x^p up(x)`.
5. A Cauchy-transform functional-differential equation and the symmetric
   Jacobi continued fraction of the up-law, with exact rational coefficients
   and the rigorous limiting coefficient `1/4`.
6. Order-statistic representations for nonlinear powers and the asymptotic
   scale `integral up(x)^p dx ~ F^{-1}(1/p)`.

Novelty statements are explicitly limited to the audited ProveIt corpus; the
report does not claim an exhaustive worldwide priority search.

## Reproduce the numerical outputs

The supplied outputs were generated with Python 3.13.5 and the package versions
in `requirements.txt`.

```bash
python -m venv .venv
. .venv/bin/activate          # Windows PowerShell: .venv\Scripts\Activate.ps1
python -m pip install -r requirements.txt
python numerical_experiments.py --output-dir reproduced
```

The program uses exact `fractions.Fraction` arithmetic for Bernoulli
cumulants, moments, Gram-Schmidt polynomials, and Jacobi coefficients. Floating
point work is used only to cross-check proved identities. No Monte Carlo
simulation is used.

## Rebuild the PDF

A TeX Live installation containing `pdflatex`, `libertinus`, `amsmath`,
`mathtools`, `booktabs`, `tabularx`, `hyperref`, and `cleveref` is sufficient.
Run from this directory:

```bash
(cd ../.. && pdflatex -interaction=nonstopmode -halt-on-error Integration_and_Transform_Frontiers.tex)
(cd ../.. && pdflatex -interaction=nonstopmode -halt-on-error Integration_and_Transform_Frontiers.tex)
(cd ../.. && pdflatex -interaction=nonstopmode -halt-on-error Integration_and_Transform_Frontiers.tex)
```

These commands update `../../Integration_and_Transform_Frontiers.pdf`.

## Verification performed for this release

- Clean LaTeX build: successful.
- Cross-references/citations: resolved.
- PDF preflight: openable, unencrypted, text-based, 25 A4 pages.
- 200-DPI visual render: checked for clipping, overlaps, broken glyphs, tables,
  equations, and figures.
- Fresh numerical rerun: generated text, LaTeX table, and all three figures
  identically to the packaged versions.

> **Editorial note (2026-08-28):** the report source (.tex) and compiled PDF listed above were removed from this directory after their content was merged into the volume `Integration_and_Transform_Frontiers.tex`; their SHA-256 hashes remain in the volume provenance section, and git history archives the files. This directory keeps only figures, data, and scripts.
