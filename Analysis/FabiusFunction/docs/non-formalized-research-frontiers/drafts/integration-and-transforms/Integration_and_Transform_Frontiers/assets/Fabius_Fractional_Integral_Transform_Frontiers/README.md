# Integral, Transform, and Fractional-Order Frontiers for the Fabius–Rvachev System

This package contains a 39-page research report, its LaTeX source, a deterministic numerical verification program, the recursive repository-audit ledger, and all generated numerical outputs.

## Main files

- `fabius_fractional_integral_transform_frontiers.tex` — complete manuscript source.
- `fabius_fractional_integral_transform_frontiers.pdf` — compiled and visually inspected PDF.
- `fractional_frontier_experiments.py` — fully commented deterministic verification program.
- `new_numerical_results.tex` — tables imported by the manuscript.
- `numerical_results.txt` — human-readable numerical ledger.
- `numerical_results.json` — machine-readable parameters and results.
- `corpus_manifest.txt` — recursive 78-path TeX audit ledger: the authoritative pinned 67-source inventory plus an 11-path live-main supplement.
- `requirements.txt` — Python package versions used for the supplied run.
- `SHA256SUMS.txt` — checksums for the distributed files.

## Scope and status

The report treats the existing probability/refinement theory, dyadic arithmetic, moment recurrences, Thue–Morse and q-binomial structure, sinc products, Lambert-W endpoint analysis, repeated integration, self-sampling, Rvachev–Appell systems, Newton/exponent-sequence results, and elementary weighted/inverse integration identities as prior inputs.

The strongest proved results not located explicitly in the audited repository corpus are:

1. Riemann–Liouville inverse-pair duality for powers of the Fabius function and inverse Fabius function.
2. Digamma- and trigamma-corrected endpoint asymptotics for fractional primitives and derivatives of `Q(y)^beta`, including the sharp strong-`L^p` boundary `sigma p <= 1`.
3. Exact exterior moment series for the fractional Laplacian and Riesz potential of Rvachev's up-function, with rational Bernoulli/Bell-generated coefficients.
4. A Fourier/sinc expression for the fractional Sobolev energy.
5. A logarithmic Cauchy-transform fixed point and an all-order resolvent hierarchy.
6. A log-periodic Floquet multiplier and cocycle repairing the obstruction to naive fractional dyadic scaling.
7. A sinc-product formula for the Gini mean difference.

The report also supplies a self-contained synthesis of ordinary antiderivatives, definite integrals, inverse-function identities, Mellin/Laplace/Fourier/Stieltjes transforms, complex and negative moments, order statistics, all integer derivative/primitive orders, and a set of clearly labeled conjectures. “New” is repository-relative and is not presented as a worldwide priority claim.

## Numerical method

The program uses no Monte Carlo sampling and no network access. It reconstructs the up-function by FFT inversion of its exact infinite sinc-product Fourier transform on a period-four grid with `2^18` points and 38 product factors. Exact centered moments are generated using `fractions.Fraction`. FFT quadrature, PCHIP inversion, Gauss–Jacobi quadrature, SciPy integration, and mpmath are used only as independent floating-point checks of analytically proved formulas.

The supplied run verifies:

- exterior fractional-Laplacian series to errors from about `4e-7` near the support to roundoff farther away;
- exterior Riesz-potential series to errors from about `4e-10` to roundoff;
- the Cauchy/log fixed point and resolvent hierarchy at roughly `1e-17` residuals;
- decreasing first-correction errors in the fractional quantile primitive and derivative endpoint tests.

## Reproduce the numerical outputs

From this directory:

```bash
python fractional_frontier_experiments.py
```

This rewrites:

```text
new_numerical_results.tex
numerical_results.txt
numerical_results.json
```

## Build the PDF

From this directory:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  fabius_fractional_integral_transform_frontiers.tex
```

The delivered PDF was built with Python 3.13.5, NumPy 2.3.5, SciPy 1.17.0, mpmath 1.3.0, pdfTeX 1.40.26, and latexmk 4.86. The build has no overfull boxes or unresolved references. The remaining messages are harmless font-size substitutions, several underfull table cells, and hyperref bookmark warnings caused by mathematics in section titles.
