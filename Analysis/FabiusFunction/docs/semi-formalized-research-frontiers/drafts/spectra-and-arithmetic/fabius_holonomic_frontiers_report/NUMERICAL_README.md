# Numerical experiment package

Run from this directory with

```bash
python frontier_experiments.py --output-dir data
```

The report build uses the already generated tables and figures under `data/`.
All holonomic-rank and collision computations use exact rational or exact
quadratic-field arithmetic. Floating point is used only for presentation,
minimum-gap ordering after exact deduplication, ODE residual diagnostics, and
plots.

Tested with Python 3.13, SymPy 1.14, mpmath 1.3, and matplotlib 3.10.
The golden-ratio recurrence reported by the script is explicitly classified in
the paper as computational evidence/conjecture, not as a proved theorem.
