# Closing the Lagrange--Rvachev Loop

This package accompanies the report
**Closing the Lagrange--Rvachev Loop: Exact cardinal synthesis by shifted
up-functions, defect-completed factorizations, convergence dichotomies, and
Lambert-scale conditioning** (29 August 2026).

## Main files

- `Lagrange_Rvachev_Loop.tex` -- complete LaTeX source.
- `Lagrange_Rvachev_Loop.pdf` -- compiled 30-page report.
- `experiments.py` -- commented exact and numerical reproducibility code.

## Generated data and figures

- `coefficient_growth.csv` -- exact rational endpoint-cardinal coefficient
  norms through degree 13.
- `numerical_summary.txt` -- numerical diagnostics printed by the script.
- `low_degree_cardinal_coefficients.tex` -- generated exact quadratic-cardinal
  amplitudes.
- `coefficient_growth.png` -- coefficient-growth diagnostic.
- `interpolation_stability.png` -- equispaced versus Chebyshev--Lobatto
  interpolation diagnostic.
- `finite_loop_demo.png` -- finite degree-4 loop reconstruction.

## Reproducing the experiments

```bash
python experiments.py
```

The tested environment used Python 3 with NumPy 2.3.5, SciPy 1.17.0,
SymPy 1.14.0, and Matplotlib 3.10.8.  Exact synthesis calculations use SymPy
rationals.  Floating-point calculations are used only for diagnostic plots.

## Compiling the report

Run from this directory:

```bash
pdflatex Lagrange_Rvachev_Loop.tex
pdflatex Lagrange_Rvachev_Loop.tex
```

The three PNG figure files must remain in the same directory as the source.
