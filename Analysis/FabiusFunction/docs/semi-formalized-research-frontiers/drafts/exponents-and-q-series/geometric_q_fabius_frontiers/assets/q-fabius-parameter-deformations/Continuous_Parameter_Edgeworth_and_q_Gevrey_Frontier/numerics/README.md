# Numerical experiments

Run from the project root with Python 3.11 or later:

```bash
python -m pip install -r requirements.txt
python numerics/fabius_q_edgeworth.py --output-dir .
```

The script is deterministic and uses no Monte Carlo sampling. It:

1. evaluates the exact infinite sinc product on an FFT frequency grid;
2. inverts it to obtain standardized densities;
3. tests Gaussian and first-, second-, and third-order Edgeworth approximations;
4. numerically inverts the CDF and tests two Cornish--Fisher corrections;
5. evaluates the exact parametric compact-scale rate and its Lambert-W support-edge asymptotic; and
6. writes all CSV files, LaTeX tables, vector PDF figures, and PNG companion figures under `data/` and `figures/`.

The product is truncated only after the largest remaining sinc argument is below the documented tolerance. Density mass and retained-factor counts are recorded in `data/edgeworth_errors.csv` as diagnostics.
