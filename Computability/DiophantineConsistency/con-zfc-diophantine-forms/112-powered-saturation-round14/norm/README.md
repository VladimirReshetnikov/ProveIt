# Norm circuit: twelve integers, degree768,141 operations

Primary literal equation: `equation.json`.
Polynomial-identical cancellation-aware certificate: `equation_reduced.json`.
Arithmetic proof: `PROOF.md`.
Full unbounded zero-existence proof: `../radicals/PROOF.md`.
Independent checks: `CHECKS.json`.

Replay:

    python build.py
    python check.py
    python -O check.py

Python dependency: SymPy. No network access is required. Fixed coefficients are fully materialized in `coefficients/`; no port is a new quantified unknown.

The polynomial has twelve unrestricted integer variables, six unchanged fixed integer leaves, exactdegree768, and141 live binary arithmetic operations. The minimal graph's naive bound is976, not768. The reduced graph gives a syntactic upper bound768 at149 operations, and explicit nonzero authentic coefficients prove attainment.

The theorem inherits the same ordinary finite-refutation/compiler calibration as the pinned scalar parent. This is not a proof that ZFC is consistent or inconsistent, a newly kernel-checked result, or a global minimum claim. Exploratory files not listed in `RELEASE_WHITELIST.json` are excluded from the release.
