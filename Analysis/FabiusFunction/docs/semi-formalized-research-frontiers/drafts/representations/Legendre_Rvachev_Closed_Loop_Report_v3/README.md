# Legendre Polynomials in the Rvachev Up Dictionary

This bundle accompanies the 33-page report

> **Legendre Polynomials in the Rvachev Up Dictionary:**  
> *Symmetric finite synthesis, closed Fourier--Legendre loops, and transmuted spectral geometry.*

## Main files

- `legendre_rvachev_closed_loop.pdf` — rendered report.
- `legendre_rvachev_closed_loop.tex` — self-contained LaTeX source; the bibliography is embedded.
- `legendre_up_experiments.py` — fully commented exact-symbolic and numerical experiment program.
- `requirements.txt` — Python package versions used for the supplied outputs.

## Reproducing the calculations

From this directory, run

```bash
python legendre_up_experiments.py
```

The exact layer uses Python integers and SymPy rationals. It reconstructs the reciprocal-MGF coefficients, the deconvolved Legendre polynomials, the central-pair endpoint matrices, the q-product determinant certificate, the exact up-function Legendre coefficients, the Favard obstruction, and the Sturm root counts. The floating-point layer generates the four diagnostic figures and the stability tables.

Python environment used for the archived outputs:

- Python 3.13.5
- NumPy 2.3.5
- SymPy 1.14.0
- Matplotlib 3.10.8

## Compiling the report

A standard TeX Live installation with `latexmk` is sufficient:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error legendre_rvachev_closed_loop.tex
```

The archived PDF was built with pdfLaTeX under TeX Live 2025. The four generated PNG files must remain in the same directory as the source.

## Exact certificates and tables

- `Q12_sturm_certificate.txt` — exact rational Sturm certificate proving that `Q_12` has eight real and four nonreal roots.
- `sturm_real_root_counts.csv` — exact real/nonreal root counts through degree 20.
- `direct_determinant_checks.csv` — direct central-pair determinant checks for the feasible exact sizes.
- `sigma_binary_partition.csv` and `sigma_sign_checks_0_128.csv` — coefficient-extraction data for the q-product determinant correction.
- `central_legendre_coefficients.csv` — exact central-pair representations of even Legendre polynomials.
- `closed_loop_central_coefficients.csv` — exact coefficients in the parity-compressed closed loop.
- `up_legendre_coefficients.csv` — exact low-order Fourier--Legendre coefficients of the up-function.
- `deconvolved_legendre_roots.csv` — high-precision numerical root data.
- `floating_point_diagnostics.csv` — cancellation and approximation diagnostics.
- `numerical_results.txt` and `favard_obstruction.txt` — human-readable exact summaries.

## Figures

- `sigma_binary_partition_ratio.png`
- `central_pair_roundoff.png`
- `legendre_partial_sum_error.png`
- `deconvolved_legendre_root_locus.png`

The exact mathematical identities do not depend on the Fourier truncations used to draw the numerical figures.
