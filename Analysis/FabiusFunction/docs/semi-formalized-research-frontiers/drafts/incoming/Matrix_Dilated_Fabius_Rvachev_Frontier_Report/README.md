# Matrix-Dilated Fabius–Rvachev Laws

This archive accompanies the report
**“Matrix-Dilated Fabius–Rvachev Laws: Infinite Box Splines, Thue–Morse Directional Derivatives, Bell–Bernoulli Tensor Resolvents, and Rotating-Zonoid q-Series.”**

The report is pinned to `VladimirReshetnikov/ProveIt` commit
`90b2d3587833dea1bc4a6bf0c36d92f7200396e6` (30 August 2026).
Its novelty claims are deliberately repository-relative, not claims of worldwide
publication priority. Proven statements, imported inputs, numerical observations,
and conjectures are visibly distinguished in the LaTeX source and PDF.

## Main files

- `matrix_dilated_fabius_rvachev.tex` — complete LaTeX source.
- `matrix_dilated_fabius_rvachev.pdf` — compiled 29-page report.
- `matrix_fabius_experiments.py` — deterministic, extensively commented
  numerical experiment suite.
- `CORPUS_AUDIT.md` — recursive-source audit and collision-search ledger.
- `figures/` — all figures in PDF and PNG form.
- `data/` — machine-readable numerical tables.
- `results/numerical_summary.txt` — compact numerical audit trail.
- `SHA256SUMS` — integrity hashes for the distributed payload.

## Principal results developed in the report

For an expansive matrix `A`, a finite vector dictionary `V`, and independent
uniform cube digits, the report studies

```text
X = sum_{n>=1} A^{-n} V U_n.
```

It proves an exact infinite-zonotope support formula, an entire matrix-Mahler
sinc product, a full-dimensionality/smoothness dichotomy with log-Gaussian
Fourier decay, log-concavity, a matrix Rvachev differential equation, finite
box-spline approximants with Bell–Bernoulli correction operators, a
multivariate Thue–Morse derivative cube and tensor Prouhet cancellation, tensor
cumulant resolvents and moment arithmetic, Appell–Koopman intertwining, exact
Legendre coefficients of projections, and infinite-zonotope volume formulas.

For the rotating planar family `A^{-1} = q R_theta`, it additionally obtains an
exact area q-series, dense-edge and curvature-measure formulas, a rational-angle
versus irrational-angle natural-boundary dichotomy, a disk-versus-polygon Abel
shape theorem, a certified central-plateau regime, finite cyclotomic formulas for
projection cumulants, and directional cap products leading back to inverse
Fabius and Lambert-W asymptotics.

## Reproduce the numerical experiments

Python 3.10 or later is recommended. In the extracted directory:

```bash
python -m pip install -r requirements.txt
python matrix_fabius_experiments.py --output-dir . --samples 180000
```

The script uses the fixed seed `20260830`, makes no network requests, and
regenerates the contents of `figures/`, `data/`, and `results/`.

## Rebuild the report

A reasonably complete TeX Live installation with `latexmk` is sufficient:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  matrix_dilated_fabius_rvachev.tex
```

The distributed PDF was rebuilt until all references and citations resolved and
LaTeX emitted no layout or package warnings. All fonts are embedded; the
Matplotlib vector figures use embedded TrueType fonts rather than Type-3 glyphs.
