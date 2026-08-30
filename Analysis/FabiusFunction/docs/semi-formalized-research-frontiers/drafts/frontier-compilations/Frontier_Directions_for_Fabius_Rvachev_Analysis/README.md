# Frontier Directions for Fabius–Rvachev Analysis

This archive contains the LaTeX source, compiled PDF, deterministic numerical experiments, generated figures, and machine-readable tables for the report dated **30 August 2026**.

## Main deliverables

- `fabius_frontier_report.tex` — complete 33-page report source.
- `fabius_frontier_report.pdf` — compiled report.
- `source/fabius_frontier_experiments.py` — fully commented, deterministic experiment suite.
- `figures/` — PDF figures used by the report and PNG preview copies.
- `data/` — CSV, TXT, and JSON outputs used for numerical checks.
- `requirements.txt` — pinned Python package versions used for the supplied run.
- `REPOSITORY_AUDIT.md` — source-audit and nonduplication methodology.
- `SHA256SUMS` — hashes for integrity checking.

## Principal results developed in the report

The report separates proved results, proof programs, numerically supported statements, and conjectures. Its main new directions relative to the inspected repository snapshot are:

1. an exact affine duality reducing every negative parameter of the geometric-uniform family to a positive one;
2. closed Bernoulli cumulants and Bell-polynomial moments for arbitrary `q`;
3. log-concavity, the exact central plateau, and signed-copy derivative formulas with exact sup norms for `0 < q <= 1/2`;
4. an entire zero divisor, spectral zeta function, universal zero density, and reciprocal-integer digit-sum zero counts for the infinite sinc product;
5. recovery of the Thue–Morse sign from cumulative zero-count parity in the dyadic case;
6. normalized `q`-moment polynomials and a positive-integral-coefficient conjecture checked through order 30;
7. Gaussian/Edgeworth, large-deviation, and Legendre heat-kernel scaling regimes as `q -> 1`;
8. an exact arbitrary-`q` dilation-periodic Laplace decomposition with Gamma–zeta Fourier coefficients, leading to general-`q` endpoint and inverse conjectures.

“Novel” in the report means **not found in the inspected repository snapshot**. It is not a claim of worldwide priority.

## Reproducing the numerical experiments

A Python 3.13 environment was used. Create an environment and install the pinned packages:

```bash
python -m venv .venv
source .venv/bin/activate        # Windows PowerShell: .venv\Scripts\Activate.ps1
python -m pip install -r requirements.txt
```

Run the complete deterministic suite from the archive root:

```bash
python source/fabius_frontier_experiments.py --output-root .
```

No random sampling is used. The program reconstructs densities by FFT from the characteristic product, uses exact polynomial recurrences for moment experiments, and switches to arbitrary precision for the cancellation-sensitive Legendre calculation.

The supplied run used:

- Python 3.13.5
- NumPy 2.3.5
- SciPy 1.17.0
- SymPy 1.14.0
- mpmath 1.3.0
- Matplotlib 3.10.8

The aggregate results are in `data/experiment_metadata.json`.

## Compiling the LaTeX report

The report uses standard TeX Live packages and reads the PDF figures from `figures/`.

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error fabius_frontier_report.tex
```

The supplied PDF was produced with pdfTeX from TeX Live 2025 and Latexmk 4.86. A direct two- or three-pass `pdflatex` build also works because the bibliography is embedded in the source.

## Integrity check

From the archive root:

```bash
sha256sum -c SHA256SUMS
```
