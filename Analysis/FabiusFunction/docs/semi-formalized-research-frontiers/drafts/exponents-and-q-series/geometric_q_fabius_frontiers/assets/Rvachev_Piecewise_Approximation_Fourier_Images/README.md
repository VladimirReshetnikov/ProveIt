> **Absorbed into the consolidated volume.**
> This directory is the preserved verification package of a report that is now
> **Part~IV** of `geometric_q_fabius_frontiers.tex`, two levels up. The
> report's own `.tex` and `.pdf` were deleted when it was merged; git history
> is the archive, and the volume's Provenance section pins the absorbed
> snapshot by SHA-256. The scripts, data, and figures here are still live —
> the volume includes them from `assets/Rvachev_Piecewise_Approximation_Fourier_Images/`. Any build or path
> instruction below describes the original standalone package and no longer
> resolves as written.

# Fourier images of the repeated-integration approximants to Rvachev's up-function

This archive accompanies the research report
`Rvachev_Piecewise_Approximation_Fourier_Images.tex` / `.pdf`.

## Contents

- `Rvachev_Piecewise_Approximation_Fourier_Images.tex` — complete LaTeX source.
- `Rvachev_Piecewise_Approximation_Fourier_Images.pdf` — compiled 27-page report.
- `fourier_piecewise_experiments.py` — commented symbolic and numerical experiments.
- `requirements.txt` — Python packages used for the reproducibility run.
- `data/` — exact CSV tables, a JSON summary, and all report figures in PDF and PNG form.
- `SHA256SUMS.txt` — checksums for the packaged files.

The LaTeX source loads its figures from `data/*.pdf`, so preserve the directory
layout when recompiling.

## Fourier convention

The report uses radian frequency

    f_hat(xi) = integral_R f(x) exp(-i xi x) dx

and `sinc(z) = sin(z)/z`.

## Reproduce the experiments

Python 3.10 or later is required. From the archive directory:

```bash
python -m venv .venv
. .venv/bin/activate                 # Windows PowerShell: .venv\Scripts\Activate.ps1
python -m pip install -r requirements.txt
python fourier_piecewise_experiments.py --output-dir data --coefficient-order 30
```

The script computes exact rational transfer coefficients with SymPy, evaluates
cancellation-sensitive quantities with mpmath, performs lobe-wise optimization
and Gauss-Legendre quadrature with SciPy/NumPy, and regenerates every figure.
A clean reproducibility run was performed before packaging; all generated CSV
and JSON outputs matched the included copies byte for byte.

## Compile the report

A TeX Live installation containing Libertinus, `amsmath`, `mathtools`,
`cleveref`, `tcolorbox`, and the standard graphics/table packages is sufficient.
Run either

```bash
latexmk -pdf Rvachev_Piecewise_Approximation_Fourier_Images.tex
```

or two ordinary `pdflatex` passes (additional passes may be needed for the table
of contents and cross-references).

The packaged PDF was built with pdfTeX 1.40.26 from TeX Live 2025/dev.

> **Editorial note (2026-08-28):** the report source and compiled PDF listed above (and, where listed, the supplied source scan/OCR) were removed from this directory after their content was merged into the volume `Exponents_and_q_Series_Frontiers.tex`; their SHA-256 hashes remain in the volume provenance list (and in `SHA256SUMS` here where present), and git history archives the files. This directory keeps only figures, data, and scripts.
