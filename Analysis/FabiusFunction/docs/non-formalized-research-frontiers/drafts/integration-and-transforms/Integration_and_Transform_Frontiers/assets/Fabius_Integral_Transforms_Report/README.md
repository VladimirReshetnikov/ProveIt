# Fabius Integral and Transform Research Report

> **Archived companion bundle.** The former standalone manuscript is now
> consolidated in `../../Integration_and_Transform_Frontiers.tex`, with the
> rendered report at `../../Integration_and_Transform_Frontiers.pdf`. This
> directory retains its supporting computations.

This package contains:

- `../../Integration_and_Transform_Frontiers.tex` - current consolidated source.
- `../../Integration_and_Transform_Frontiers.pdf` - compiled consolidated report.
- `experiments.py` - commented exact/numerical experiment code.
- `numerical_results.json` - machine-readable output from the experiments.
- `numerical_results.tex` - generated LaTeX table included by the report.

Rebuild the consolidated report from this directory with three passes:

```bash
(cd ../.. && pdflatex -interaction=nonstopmode -halt-on-error Integration_and_Transform_Frontiers.tex)
(cd ../.. && pdflatex -interaction=nonstopmode -halt-on-error Integration_and_Transform_Frontiers.tex)
(cd ../.. && pdflatex -interaction=nonstopmode -halt-on-error Integration_and_Transform_Frontiers.tex)
```

These commands update `../../Integration_and_Transform_Frontiers.pdf`.

Reproduce the numerical data with:

```bash
python experiments.py --moments 12000 --cutoff 500
```

Dependencies: Python 3.10+, NumPy, SciPy, and mpmath.

The term “new” in the report means not found in the recursively audited ProveIt
LaTeX corpus at the time of writing; it is not a worldwide-priority claim.
