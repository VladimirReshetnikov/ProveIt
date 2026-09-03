> **Absorbed into the consolidated volume.**
> This directory is the preserved verification package of a report that is now
> **Part~VI** of `geometric_q_fabius_frontiers.tex`, two levels up. The
> report's own `.tex` and `.pdf` were deleted when it was merged; git history
> is the archive, and the volume's Provenance section pins the absorbed
> snapshot by SHA-256. The scripts, data, and figures here are still live —
> the volume includes them from `assets/Atomic_Functions_Beyond_Dyadic_Frontiers/`. Any build or path
> instruction below describes the original standalone package and no longer
> resolves as written.

# Atomic Functions Beyond the Critical Dyadic Case

This archive contains the English reconstruction and expansion of the attached Russian Rvachev chapter on atomic functions, together with numerical experiments used to audit the report's formulas.

## Main deliverables

- `Atomic_Functions_Beyond_Dyadic_Frontiers.tex` — complete LaTeX source.
- `Atomic_Functions_Beyond_Dyadic_Frontiers.pdf` — compiled 40-page report.
- `experiments.py` — reproducible numerical experiments, figures, and CSV audits.
- `figures/` — vector PDF and raster PNG versions of all eight figures.
- `data/` — machine-readable validation tables.
- `source_notes/` — the OCR TeX and surviving printed source pages used for the reconstruction.
- `SHA256SUMS` — checksums for the archive contents.

## Mathematical scope

The report reconstructs the source's Fourier-product existence criterion, the generalized densities

\[
\widehat h_a(t)=\prod_{j\ge 1}\operatorname{sinc}(t a^{-j}),
\]

the probability representation, moment recurrences, the separated spline regime `a>2`, the critical Rvachev `up` function at `a=2`, exact dyadic values, Thue–Morse derivative signs, polynomial reproduction, and the opening of the `Fup` hierarchy.

The expansion connects these topics to infinite convolutions, nonuniform box splines, refinement equations, Bernoulli and Bell polynomials, Lambert series, `q`-Pochhammer and Stieltjes–Wigert structures, fractal strings, Mellin transforms, Gamma–zeta periodic corrections, and the lower branch `W_{-1}` of the Lambert W function.

The formulas marked `[F]` in the report are frontier claims relative to the audited repository snapshot, not universal historical-priority claims. The principal post-audit additions are:

- defective equimeasurability and the complete `L^p` derivative ladder for every `a>=2`;
- an exact derivative-energy factorization, Bernoulli-convolution weak limit, support convergence, and Rényi/Shannon entropy law;
- a continuous-base sinc-product family of non-lognormal representatives for scaled Stieltjes–Wigert moment problems;
- the corresponding `q`-Pearson, Hankel determinant, and monic orthogonal-polynomial formulas.

## Reproducing the numerical material

A Python 3 environment with the packages in `requirements.txt` is sufficient:

```bash
python -m pip install -r requirements.txt
python experiments.py --output .
```

The script uses the fixed seed `20260828`. It writes all figures to `figures/` and all validation tables to `data/`. SciPy is not required.

## Compiling the report

A recent TeX Live installation with `latexmk` is recommended:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  Atomic_Functions_Beyond_Dyadic_Frontiers.tex
```

To remove auxiliary build files afterward:

```bash
latexmk -c Atomic_Functions_Beyond_Dyadic_Frontiers.tex
```

The figures referenced by the LaTeX source are already included, so regenerating them is optional.

## Proof-status legend

- `[S]` — translated or cleanly reconstructed from the attached source.
- `[R]` — already present in the audited repository or established literature.
- `[N]` — proved in the report, without by itself asserting priority.
- `[F]` — post-audit frontier formula not found in the inspected repository snapshot or focused comparison.
- `[C]` — conjecture or proposed research program.

## Numerical audit highlights

The supplied tables record, among other checks:

- periodicity residuals for the general-base Laplace correction below `4.5e-15`;
- Gamma–zeta Fourier-mode absolute discrepancies below `3.2e-12`;
- relative quadrature errors below `8e-11` for the first five normalized spectral moments at `a=2.6`;
- Monte Carlo agreement with Bell-polynomial moments through order ten;
- empirical convergence of derivative-energy measures to the associated Cantor/Bernoulli law.

> **Editorial note (2026-08-28):** the report source (.tex), compiled PDF, and the source-material copies of the Russian scan/OCR listed above were not carried into this directory: the report content was merged into the volume `Exponents_and_q_Series_Frontiers.tex`, the scan/OCR copies are byte-identical to the previously recorded ones (same SHA-256, recorded in the volume provenance), and git history archives the absorbed archive. This directory keeps only figures, data, and scripts.
