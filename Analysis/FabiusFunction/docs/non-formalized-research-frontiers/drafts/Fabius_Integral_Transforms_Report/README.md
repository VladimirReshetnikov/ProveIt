# Fabius Integral and Transform Research Report

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
