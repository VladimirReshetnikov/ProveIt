# Dyadic-Comb Quadrature for the Fabius and Rvachev Functions

This archive accompanies the research report prepared on 28 August 2026.

## Contents

- `fabius_dyadic_comb_report.tex` — complete LaTeX source.
- `fabius_dyadic_comb_report.pdf` — compiled 25-page report.
- `fabius_dyadic_comb_experiments.py` — commented, self-contained exact-arithmetic experiments, plus optional high-precision fractional-power tests.
- `numerical_results.txt` — captured output from the experiment script.
- `SHA256SUMS.txt` — checksums for integrity verification.

## Principal results in the report

The report proves, among other statements:

1. Exact shifted dyadic-comb quadrature for every polynomial of degree at most the mesh depth `m` against Rvachev's `up` function.
2. A finite 2-adic alias decomposition, a closed first-failure formula, special superconvergent shifts, and Bell–Bernoulli formulas for higher Fourier jets.
3. Exact stabilization of the one-sided Fabius comb for natural powers at the parity threshold `m >= 2 ceil(p/2)`.
4. An all-depth finite Hurwitz-zeta–Thue–Morse formula for complex powers.
5. Universal zeta/Hurwitz-zeta corrections for fractional powers and Mellin-renormalized formulas for negative powers.
6. Closed binomial-kernel formulas for arbitrary-order iterated sums, with exact full-support reductions to moments.

Claims of novelty are made relative to the audited ProveIt documentation tree, not as universal bibliographic priority claims. Conjectures are labeled as such in the report.

## Reproduce the numerical experiments

Exact tests require only Python 3.10 or later:

```bash
python fabius_dyadic_comb_experiments.py --skip-fractional
```

The fractional-power tables additionally use `mpmath`:

```bash
python -m pip install mpmath
python fabius_dyadic_comb_experiments.py > numerical_results.txt
```

The exact tests use `fractions.Fraction`; no floating-point tolerance is used. The script verifies stabilization thresholds through `p=10`, shifted polynomial exactness and phase superconvergence, independent all-depth formulas, and selected iterated sums.

## Recompile the report

With a standard TeX Live installation:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error fabius_dyadic_comb_report.tex
```

The supplied PDF was compiled with pdfLaTeX, passed structural preflight, and was visually inspected after rendering all 25 pages.

> **Editorial note (2026-08-28):** the report source (.tex) and compiled PDF listed above were removed from this directory after their content was merged into the volume `Dyadic_Comb_Frontiers.tex`; their SHA-256 hashes remain in the volume provenance section, and git history archives the files. This directory keeps only figures, data, and scripts.
