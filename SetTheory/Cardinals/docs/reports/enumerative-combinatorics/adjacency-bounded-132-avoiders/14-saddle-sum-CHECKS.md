# Reproducible checks

Run:

    python verify_saddle_algebra.py
    python -O verify_saddle_algebra.py

The exact checker independently differentiates the second derivative of the count action twice. It checks every coefficient in the third and fourth derivatives, the constants 1/24 and 1/192, and 54 rational normalizations of the common saddle prefactor. It uses explicit exceptions, so optimized Python does not disable the checks.

Optionally run:

    python saddle_diagnostics.py

This diagnostic uses NumPy and SciPy. It solves the finite Catalan root, computes the scalar squared-renewal coefficient from a positive renewal recurrence, and compares it with exact-tilt saddle terms. Twenty rows use m = 128, 256, 512, 1024, at five representative length scales. Their chosen numerical tilt interval is [-0.8, 1] and cutoff is floor(m/64); these are finite diagnostics, not an explicit universal choice of the theorem's existence constants.

The observed saddle-to-scalar ratios range approximately from 0.915 to 1.103. No finite error threshold is asserted. These numbers are not theorem evidence, do not establish uniformity over the theorem's parameter range, and do not compute actual avoidance counts at the sampled lengths. The analytic proof supplies the required estimates.

