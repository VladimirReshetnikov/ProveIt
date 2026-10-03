# Checks and diagnostics

Exact standard-library regression:

    python3 checks/verify_summand_ratio.py

This verifies 200 rational instances of the adjacent Gamma-summand identity
after removing its common exponential and square-root factors. It writes
summand_ratio_results.json. These checks verify algebraic normalization,
not an asymptotic statement.

Optional scalar-envelope diagnostics:

    python3 checks/gamma_sum_diagnostics.py

This requires NumPy and SciPy and writes gamma_sum_diagnostics.json. It
computes the scalar root and squared-renewal coefficients, then records
36 finite comparisons with the Gamma sum. The stored environment versions
are in the output. Finite ratios can be far from one; the script does not
assert a finite approximation bound, convergence rate, or effective cutoff.
It does not compute the full actual-avoider count at these larger sizes.

The diagnostic sum uses positive deficits through 60. On its sampled c
range [0.1,1.2], it is the theorem's admissible window with a=exp(-250),
b=60: the maximum defining B_* is less than11, J_0.1(a)>24.7, and
J_1.2(60)>24, so both required margins exceed B_*+10. The extrema reduce
to endpoints by elementary convexity. Every positive sampled deficit
exceeds a. These deliberately loose constants illustrate a valid fixed
window and are not optimized.

No numerical comparison replaces the uniform tilted-coefficient,
composition, residual-domination, or injection proofs in the manuscript.
