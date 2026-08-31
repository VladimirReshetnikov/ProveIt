# Fabius--Rvachev frontier report (30 August 2026)

This package contains the LaTeX source, compiled PDF, reproducible numerical code, generated CSV/LaTeX tables, and vector plus PNG figures for:

**Continuous-Parameter Edgeworth Theory, Large Deviations, and Quadratic q-Gevrey Regularity at the Fabius--Rvachev Frontier**

## Build the report

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error fabius_frontier_report.tex
```

## Reproduce the numerical experiments

Python 3.11 or later is recommended.

```bash
python -m pip install -r requirements.txt
python numerics/fabius_q_edgeworth.py --output-dir .
```

The script is deterministic. It performs FFT inversion of the exact infinite sinc-product characteristic function, computes central quantiles, evaluates the exact parametric large-deviation rate, and regenerates every file under `data/` and `figures/`.

## Integrity

`MANIFEST.txt` lists the distributed files. `SHA256SUMS` records the SHA-256 hash of every other distributed file. The report states precisely which claims are proved, which are numerical checks, and which are conjectural. Novelty assertions are relative to the audited repository corpus, not claims of global publication priority.
