# Matrix-Dilated Fabius–Rvachev Laws

This archive accompanies the report
**“Matrix-Dilated Fabius–Rvachev Laws: Infinite Box Splines, Thue–Morse Directional Derivatives, Bell–Bernoulli Tensor Resolvents, and Rotating-Zonoid q-Series.”**

The report is pinned to `VladimirReshetnikov/ProveIt` commit
`90b2d3587833dea1bc4a6bf0c36d92f7200396e6` (30 August 2026).
Its novelty claims are deliberately repository-relative, not claims of worldwide
publication priority. Proven statements, imported inputs, numerical observations,
and conjectures are visibly distinguished in the LaTeX source and PDF.

## Main files

- `matrix_dilated_fabius_rvachev.tex` — complete 1,997-line, 76,958-byte
  LaTeX source; SHA-256
  `5311ff92a6d6d430f3c6e94d61974ffb549a8fe99bb20636a5c47116ad7d9aba`.
- `matrix_dilated_fabius_rvachev.pdf` — synchronized 29-page, 878,932-byte
  report; SHA-256
  `1c7ca0f14f2b456c4bd9692057b63f0941b15ee0810c6f1a3947a2a128a9c76b`.
- `matrix_fabius_experiments.py` — deterministic, extensively commented
  numerical experiment suite.
- `CORPUS_AUDIT.md` — recursive-source audit and collision-search ledger.
- `figures/` — all figures in PDF and PNG form.
- `data/` — machine-readable numerical tables.
- `results/numerical_summary.txt` — compact numerical audit trail.
- The former distributed-payload checksum ledger is retired and recoverable
  from Git history.

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

A reasonably complete TeX Live installation is sufficient. From clean
auxiliaries, run exactly three serial passes:

```bash
pdflatex -interaction=nonstopmode -halt-on-error matrix_dilated_fabius_rvachev.tex
pdflatex -interaction=nonstopmode -halt-on-error matrix_dilated_fabius_rvachev.tex
pdflatex -interaction=nonstopmode -halt-on-error matrix_dilated_fabius_rvachev.tex
```

The synchronized repository PDF was rebuilt by that exact procedure on
2026-09-04. Starting from absent auxiliaries, the three successful
halt-on-error passes produced 28 pages/867,730 bytes, 29 pages/878,931 bytes,
and 29 pages/878,932 bytes. All pages are A4 at rotation zero, rendered, and
contain extractable text. The final log has no TeX error, unresolved reference
or citation, or rerun request. All 29 font rows are embedded and subset, eight
are Libertinus, and none is Type 3. Title, author, subject, and keywords
metadata are present. Physical pages 1, 16, 17, 19, 21--24, and 29 passed
visual inspection, covering the title, all six figures, the repaired Section
11 running heads, and the references. Generated sidecars were removed, and no
package-local checksum ledger is a live publication gate.
