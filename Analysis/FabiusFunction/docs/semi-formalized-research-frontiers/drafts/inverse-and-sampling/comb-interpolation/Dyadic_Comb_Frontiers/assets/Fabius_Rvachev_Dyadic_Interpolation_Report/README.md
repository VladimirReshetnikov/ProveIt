# Fabius--Rvachev dyadic-comb interpolation report

This archive accompanies the research report

**Global Polynomial Interpolation of the Fabius and Rvachev Functions on Dyadic Combs: Exact arithmetic, Runge instability, endpoint-jet deflation, and frontier conjectures**

prepared on 28 August 2026.

## Main files

- `fabius_dyadic_interpolation_report.pdf` — rendered 25-page report.
- `fabius_dyadic_interpolation_report.tex` — complete LaTeX source.
- `fabius_dyadic_interpolation_experiments.py` — fully commented, reproducible high-precision experiments.
- `results/*.csv` — numerical tables used in the report.
- `figures/*.pdf` — publication-ready vector figures used by the LaTeX source.
- `RUN_METADATA.txt` — disclosed validation-grid resolutions.
- `pdf_inspection.txt` — PDF preflight information.

The report distinguishes proved theorems, numerical observations, and conjectures. Its main new construction is the endpoint-Hermite family

\[
H_{N,r}(x)=S_r(x)+[x(1-x)]^{r+1}I^{\circ}_{N-2}
\!\left(\frac{F-S_r}{[x(1-x)]^{r+1}}\right)(x),
\]

whose case `r=0` is ordinary global Lagrange interpolation. The report proves exponential instability for every fixed endpoint order and, more strongly, for every order schedule `r=r_N`; it also documents the large finite-`N` postponement obtainable near the balancing order.

## Reproducing the computations

Python 3.10 or later is recommended.

```bash
python -m pip install -r requirements.txt
python fabius_dyadic_interpolation_experiments.py --outdir quick_check --quick
```

The quick mode is a reproducibility smoke test. The full high-precision run writes the report tables and figures and may take several minutes or longer, depending on hardware:

```bash
python fabius_dyadic_interpolation_experiments.py --outdir regenerated
```

The input values `F(a/2^e)` and the derivative samples are computed exactly as rational numbers. Only the final evaluation of the interpolating polynomials uses arbitrary-precision floating-point arithmetic through `mpmath`.

## Recompiling the PDF

The supplied vector figures are already present. From the archive root:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  fabius_dyadic_interpolation_report.tex
```

The numerical maxima in the tables are sampled lower bounds on the true uniform errors, with grid resolutions documented in `RUN_METADATA.txt`; they are not claimed to be interval-certified maxima.

> **Editorial note (2026-08-28):** the report source (.tex) and compiled PDF listed above were removed from this directory after their content was merged into the volume `Dyadic_Comb_Frontiers.tex`; their SHA-256 hashes remain in the volume provenance section, and git history archives the files. This directory keeps only figures, data, and scripts.
