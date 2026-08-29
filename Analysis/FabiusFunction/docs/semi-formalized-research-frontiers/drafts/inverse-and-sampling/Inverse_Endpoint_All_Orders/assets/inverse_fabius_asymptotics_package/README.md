# Complete small-argument asymptotics of the inverse Fabius function

This package contains the LaTeX source, rendered PDF, reproducible symbolic and
numerical experiments, exact dyadic test data, and both report figures.

## Main result

For `T = log(1/y)`, `L = log(2)`, `beta = 1/L + 1/2`, and the sharp endpoint
constant `Csharp`, define

```text
H      = T + Csharp + L beta^2/2
Omega  = omega(4H + log(2L))
w      = sqrt(Omega/(2L))
theta  = w + beta
G_W(y) = theta exp(-L theta)
```

where `omega(s) + log(omega(s)) = s`. The report derives

```text
F^{-1}(y) / G_W(y) ~ 1 + sum_{m>=1} g_m(theta)/w^m
```

with a direct bivariate Lagrange-Buermann coefficient formula for every
periodic coefficient `g_m`. The first two are

```text
g_1 = -Psi(theta)

g_2 = 5/24
      + Psi(theta)(1-Psi'(theta))/L
      + (Psi''(theta)+Psi'(theta)^2)/(2L^2)
      + Psi(theta)^2/2.
```

## Files

- `inverse_fabius_asymptotics.pdf` - 20-page report.
- `inverse_fabius_asymptotics.tex` - self-contained LaTeX source.
- `inverse_fabius_experiments.py` - exact dyadic arithmetic, Fourier
  evaluation, Wright-omega solver, comparison code, plots, and SymPy
  coefficient reconstruction.
- `data/` - generated CSV and text outputs.
- `figures/` - PNG and PDF figures.
- `CORPUS_AUDIT.txt` - pinned repository scope and moving-head comparison.
- `SHA256SUMS.txt` - checksums for every packaged file except itself.

## Reproduction

Install dependencies:

```bash
python -m pip install -r requirements.txt
```

Regenerate data and figures into a temporary output directory:

```bash
python inverse_fabius_experiments.py \
  --dps 100 --modes 9 --symbolic-order 3 \
  --output-dir reproduced
```

Compile the report from the package root:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  inverse_fabius_asymptotics.tex
```

The checked-in TeX compiles immediately: the two PNG figures are included under
`data/`. Running the Python program with `--output-dir data` regenerates them.
PDF copies are also retained under `figures/` for convenient standalone use.

The report is pinned to repository commit
`ad82c27ffc6f90b3406f46c130c86d3cb83c6225`; see `CORPUS_AUDIT.txt`.

> **Editorial note (2026-08-28):** the report source (.tex) and compiled PDF listed above were removed from this directory after their content was merged into the volume `Inverse_Endpoint_All_Orders.tex`; their SHA-256 hashes remain in the volume provenance section, and git history archives the files. This directory keeps only figures, data, and scripts.
