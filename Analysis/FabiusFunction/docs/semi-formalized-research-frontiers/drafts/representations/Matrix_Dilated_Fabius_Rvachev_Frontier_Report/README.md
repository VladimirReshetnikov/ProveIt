# Matrix-Dilated Fabius–Rvachev Laws

This archive accompanies the report
**“Matrix-Dilated Fabius–Rvachev Laws: Infinite Box Splines, Thue–Morse Directional Derivatives, Bell–Bernoulli Tensor Resolvents, and Rotating-Zonoid q-Series.”**

The report is pinned to `VladimirReshetnikov/ProveIt` commit
`90b2d3587833dea1bc4a6bf0c36d92f7200396e6` (30 August 2026).
Its novelty claims are deliberately repository-relative, not claims of worldwide
publication priority. Proven statements, imported inputs, numerical observations,
and conjectures are visibly distinguished in the LaTeX source and PDF.

## Main files

- `matrix_dilated_fabius_rvachev.tex` — complete 1,998-line, 77,011-byte
  LaTeX source; SHA-256
  `f3559354efacdd5381970a67605c2e2a669c941abac6d93c080e5352ae11f2ba`.
- `matrix_dilated_fabius_rvachev.pdf` — compiled 29-page, 879,300-byte
  report; SHA-256
  `cddcba19904319507a0e93d6e447583a15dfaa25054ff0e4fabc45f8e3070741`.
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

The repository PDF was rebuilt by that exact procedure on 2026-08-31. It has
29 A4 pages, all at rotation zero and nonblank; the three passes produced 28,
29, and 29 pages. The final log is clean: all
references and citations resolved, with no rerun request, overfull or underfull
box, or package warning. All 29 font rows are embedded and subset, eight are
Libertinus, and none is Type 3. Title, author, subject, and keywords metadata
are present. Physical pages 1, 16, 17, 19, 21--24, and 29 passed visual
inspection, covering the title, all six figures, the repaired Section 11
running heads, and the references.
