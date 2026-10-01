# Verification and diagnostics

Run the exact regression suite from the package directory:

    python3 checks/verify_envelopes.py

It uses only the standard library and asserts the credited model's SHA-256.
It reconstructs the lower and squared upper renewal coefficients, compares
them to exact endpoint counts for m=1,...,20 and n=1,...,80, checks equality
with Catalan counts through degree m+1, and checks the uniform Catalan block
coefficient defect through m=256. It writes envelope_results.json beside the
script. Counts at the largest n and hashes of each full coefficient row are
recorded. Expected totals: 1600 upper comparisons, 1520 lower comparisons,
230 Catalan equalities, and 32895 uniform coefficient checks.

Optional diagnostics:

    python3 checks/probe_cluster.py

This requires NumPy and SciPy and writes cluster_diagnostics.json. It checks
scalar root residuals and records the small-jump mass, clustered mean and
variance, and root-corridor diagnostics at m=32,...,4096. These floating-point
values are illustrative and are not certificates of an asymptotic cutoff or
uniform analytic error. The exact suite and the diagnostics verify different
things; neither replaces the manuscript's all-index proofs.

model.py is inherited verbatim and is credited in SOURCES.md. The other two
scripts were prepared for this report. No third-party library is vendored.
