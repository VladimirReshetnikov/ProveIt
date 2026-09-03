> **Absorbed into the consolidated volume.**
> This directory is the preserved verification package of a report that is now
> **Part~XI** of `geometric_q_fabius_frontiers.tex`, two levels up. The
> report's own `.tex` and `.pdf` were deleted when it was merged; git history
> is the archive, and the volume's Provenance section pins the absorbed
> snapshot by SHA-256. The scripts, data, and figures here are still live —
> the volume includes them from `assets/q-fabius-parameter-deformations/Continuous_Parameter_Edgeworth_and_q_Gevrey_Frontier/`. Any build or path
> instruction below describes the original standalone package and no longer
> resolves as written.

# Fabius--Rvachev frontier report (30 August 2026)

This package contains the LaTeX source, compiled PDF, reproducible numerical code, generated CSV/LaTeX tables, and vector plus PNG figures for:

**Continuous-Parameter Edgeworth Theory, Large Deviations, and Quadratic q-Gevrey Regularity at the Fabius--Rvachev Frontier**

## Build the report

```bash
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error fabius_frontier_report.tex
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error fabius_frontier_report.tex
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error fabius_frontier_report.tex
```

The retained publication artifact was rebuilt from the 1,372-line source in
exactly three serial passes on 31 August 2026.  It is a 726,216-byte, 29-page
A4 PDF with extractable text and no encryption.  All 33 font rows are embedded
and subset; six are Libertinus rows and six are Type-3 rows inherited from the
three included Matplotlib vector figures.  The standalone figure PDFs contain
the same six Type-3 rows, so figure-font normalization remains outstanding.
The subsequent hierarchy move changed only the relative path of the shared
notation include; the PDF was intentionally not rebuilt.

## Reproduce the numerical experiments

Python 3.11 or later is recommended.

```bash
python -m pip install -r requirements.txt
python numerics/fabius_q_edgeworth.py --output-dir .
```

The script is deterministic. It performs FFT inversion of the exact infinite sinc-product characteristic function, computes central quantiles, evaluates the exact parametric large-deviation rate, and regenerates every file under `data/` and `figures/`.

## Integrity

`MANIFEST.txt` lists the distributed files. The path-adjusted source has
SHA-256
`e9d99619992f78050326249272b18f5941f659dea0f022522b23ec218953d5bf`.
The retained pre-move PDF has SHA-256
`e58548ebb28e613b493fe090271c86242a4c311536ddbbeb7317f91ab2283e77`;
it has the same mathematical content but is not byte-synchronized with the
path-adjusted driver.
`SHA256SUMS` records and verifies all 19 current payloads. The report states
precisely which claims are proved, which are numerical checks, and which are
conjectural. Novelty assertions are relative to the audited repository corpus,
not claims of global publication priority.
