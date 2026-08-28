# Fabius Integral and Transform Research Report

> **Consolidation note.** The standalone report source and PDF were absorbed
> into Part IV of the
> [consolidated volume](../../Integration_and_Transform_Frontiers.tex). This
> directory now contains only supporting assets; Git history preserves the
> former standalone files.

This package contains:

- `Fabius_Integral_Transforms_Report.tex` - LaTeX source.
- `Fabius_Integral_Transforms_Report.pdf` - compiled report.
- `experiments.py` - commented exact/numerical experiment code.
- `numerical_results.json` - machine-readable output from the experiments.
- `numerical_results.tex` - generated LaTeX table included by the report.

Reproduce the numerical data with:

```bash
python experiments.py --moments 12000 --cutoff 500
```

Dependencies: Python 3.10+, NumPy, SciPy, and mpmath.

The term “new” in the report means not found in the recursively audited ProveIt
LaTeX corpus at the time of writing; it is not a worldwide-priority claim.
