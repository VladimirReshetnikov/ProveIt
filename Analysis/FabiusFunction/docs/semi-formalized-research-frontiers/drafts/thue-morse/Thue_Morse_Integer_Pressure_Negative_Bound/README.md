# An asymptotic lower bound for the first negative pressure degree

The six-page article proves that, for every sufficiently large integer m, all even pressure coefficients at degrees 2m < N <= 6.6m are strictly positive. Therefore the first negative even degree N_m above the cancellation at 2m satisfies liminf N_m/m >= 6.6.

The threshold in m is existential. The package does not claim a numerical cutoff, an exact formula for N_m, or convergence of N_m/m. The separately certified interval (6.662966, 6.662968) concerns a positive comparison model, not the true limiting slope.

This is an unrefereed mathematical proof with exact rational scalar certificates, not a Lean formalization.

## Contents

- `article.pdf` and `article.tex`: the theorem, complete new third-cluster proof, full-disk quadratic estimate, and uniform saddle comparison
- `checks/verify_eventual_66.py`: exact endpoint-rate and norm side conditions
- `checks/verify_model_crossing.py`: optional exact bracket for the comparison-model crossing
- `checks/exact_intervals.py`: outward integer intervals, Machin pi bounds, and Taylor trigonometric bounds
- `checks/*_certificate.json`: reproducible exact outputs
- `inputs/all_integer_orders.pdf` and `.tex`: unchanged preceding report containing the full weighted Green argument and the all-m positivity theorem below 6m
- `inputs/all_integer_orders_sources.zip`: the unchanged reproducible source archive for that preceding report, including its dyadic tangent proof and scalar certificates
- `inputs/infinite_sign_changes.pdf`: unchanged preceding proof that N_m exists for every m >= 2
- `inputs/repository_integer_pressure.tex`: pinned repository source
- `PROVENANCE.md` and `SHA256SUMS`: source identity and content hashes

## Replay

Python3 with the standard library is sufficient for both new scalar checkers:

    python3 checks/verify_eventual_66.py
    python3 checks/verify_model_crossing.py

All failure checks use explicit exceptions and remain active under Python's optimization flag. The second checker imports the first and therefore also replays its conditions. Outputs use exact rational strings; no floating-point calculation enters either certificate. The small proposed saddle brackets are checked, not trusted.

A conventional TeX Live installation with pdfLaTeX, AMS packages, geometry, Latin Modern, microtype, hyperref and xurl can build `article.tex`. The included `build_local.sh` also supports the explicit TeX/font paths of the production environment. It performs two passes and writes `article.pdf`.

The analytic local-limit argument establishes a common sufficiently large threshold but does not compute it. Passing these scalar scripts should not be described as a finite verification of all smaller m.
