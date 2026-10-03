# Checks and finite diagnostics

Run:

    python verify_exact_identities.py
    python -O verify_exact_identities.py

This standard-library checker reconstructs powers of the Catalan series by integer convolution and compares 610 coefficients with the exact Lagrange-inversion formula, including the probability normalization. It also verifies 40 adjacent-Gamma ratios over rational deficits. Explicit exceptions keep all checks active under optimized Python.

Optional:

    python scalar_diagnostics.py

This requires NumPy and SciPy. It computes finite critical scalar coefficients by a positive renewal recurrence, for m = 128, 512, 2048 and 4096, at ordinary and near-transition phases. Twenty rows are saved.

These samples are visibly pre-asymptotic: their counts are only four or five, and their count/log(m) ratios are not yet small. The ordinary single-Gamma-to-exact ratios range approximately from 0.076 to 0.519, and the transition two-Gamma-to-exact ratios from 0.358 to 0.656. No numerical agreement threshold, convergence rate, or finite error bound is claimed. These computations are included for reproducibility and future larger-parameter comparison. They do not count actual avoiders at those lengths and do not establish any theorem.

The uniform conclusions come from the analytic composition, maximal-atom and weighted-tail estimates in the manuscript.

