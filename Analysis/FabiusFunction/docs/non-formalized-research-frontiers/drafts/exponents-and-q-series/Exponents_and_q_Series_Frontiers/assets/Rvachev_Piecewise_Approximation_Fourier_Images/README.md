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
