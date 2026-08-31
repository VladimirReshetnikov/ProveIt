# Fabius--Rvachev frontier report (30 August 2026)

This package contains the LaTeX source, compiled PDF, reproducible numerical code, generated CSV/LaTeX tables, and vector plus PNG figures for:

**Continuous-Parameter Edgeworth Theory, Large Deviations, and Quadratic q-Gevrey Regularity at the Fabius--Rvachev Frontier**

## Build the report

```bash
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error fabius_frontier_report.tex
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error fabius_frontier_report.tex
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error fabius_frontier_report.tex
```

The current publication artifact was rebuilt from the 1,372-line source in
exactly three serial passes on 31 August 2026.  It is a 726,216-byte, 29-page
A4 PDF with extractable text and no encryption.  All 33 font rows are embedded
and subset; six are Libertinus rows and six are Type-3 rows inherited from the
three included Matplotlib vector figures.  The standalone figure PDFs contain
the same six Type-3 rows, so figure-font normalization remains outstanding.

## Reproduce the numerical experiments

Python 3.11 or later is recommended.

```bash
python -m pip install -r requirements.txt
python numerics/fabius_q_edgeworth.py --output-dir .
```

The script is deterministic. It performs FFT inversion of the exact infinite sinc-product characteristic function, computes central quantiles, evaluates the exact parametric large-deviation rate, and regenerates every file under `data/` and `figures/`.

## Integrity

`MANIFEST.txt` lists the distributed files. `SHA256SUMS` records the SHA-256 hash of every other distributed file and verifies the current package. The report states precisely which claims are proved, which are numerical checks, and which are conjectural. Novelty assertions are relative to the audited repository corpus, not claims of global publication priority.
