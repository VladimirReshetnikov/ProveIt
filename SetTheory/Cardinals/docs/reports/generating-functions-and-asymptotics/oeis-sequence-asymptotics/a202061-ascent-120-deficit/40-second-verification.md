# Verification and dependency boundary

## New proved mathematical content

1. The coefficient lower bound uses balanced length boxes and symmetric good increment bridges. Exact length and return constraints are imposed. The good bridge probability is controlled before conditioning, then divided by a polynomial conditioning lower bound. Jensen's inequality uses centered marginals without incorrectly assuming coordinate independence after conditioning. Legality and every seed/rounding error are controlled through O(F/log n).
2. The coefficient upper bound uses a finite-n affine calibration, a height-dependent logarithmic potential, and explicit log^(-12) endpoint cutoffs. Transformed rows contract uniformly, including small heights, long lengths and large increments. Exact terminal weights are retained. Errors are bounded through O(F/log n).
3. The inverse corollary follows by substitution and monotonic bracketing at its displayed error scale.
4. The finite-height constant has its own audit. The exact square-root amplitude and endpoint Laplace sum identify the unrestricted row threshold, and a centered sine test transfers it to the finite-height Perron threshold without boundary error.

The individual source audits are in `audit/`. The integrated article review pins the wrapper and all five included TeX files. The source proof note hashes are independently recorded in `audit/audited-source-sha256.txt`.

## Deterministic checks

`checks/second_order_checks.py` verifies the softened-potential second derivative, exact 7/3 expansion algebra, leading constant identities, the sine-square energy identity, 340 finite centered-interval convolution tests, a finite symmetric good-bridge cancellation example, exact rational reciprocal estimates under balance conditioning, and the negative powers of n in the row Taylor remainders.

`audit/check_finite_height_amplitude.py` independently extracts the square-root amplitude from the exact quadratic, reduces the identity modulo the algebraic defining cubic, and evaluates the resulting constants. All imported exact algebraic, operator, coefficient, positive-walk, and staircase checks are rerun. The recorded output is `producer-replay.txt`.

## Frozen dependency integrity

The entire manifest of the previous sharp report is copied without modification, including its nested foundation. `checks/check_dependencies.py` pins the manifest digest and verifies all 62 declared payload files and the exact non-cache file set. The imported manifest checker and foundation manifest are also rerun. No original report or audit is modified.

## Artifact verification

The 16-page PDF compiles twice with fixed timestamps, no overfull boxes and no unresolved citations or cross-references. All pages are rasterized and inspected, with detailed inspection of dense formula pages and the conjectural-outlook labeling. Build/render caches are excluded from the release.

The final release ZIP is deterministic, has a companion SHA-256 file, and contains the exact `SHA256SUMS` payload. The release generator checks integrated hash signoff before creating either the manifest or archive.

## Exclusions

These finite checks are not formal proof verification and do not establish asymptotic statements by experiment. The global coefficient at F/log n, the conjectural outlook, a multiplicative coefficient amplitude, and an all-orders transseries remain unproved.
