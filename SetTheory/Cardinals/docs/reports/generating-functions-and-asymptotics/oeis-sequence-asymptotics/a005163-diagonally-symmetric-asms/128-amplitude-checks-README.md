# Independent exact finite companion

This directory supports Report 128 with reproducible **finite** identities. It is not a proof of any infinite-size limit, little-o estimate, Fredholm convergence, weighted tightness, analytic continuation, or common amplitude. Those are established by the report's analytic arguments and cited inputs.

## Offline execution

Python 3.9 or later, standard library only. No package installation, network, external algebra system, numerical quadrature, producer checker, or predecessor output is used.

From the package directory:

    PYTHONDONTWRITEBYTECODE=1 python checks/check_exact.py
    PYTHONDONTWRITEBYTECODE=1 python -O checks/check_exact.py
    PYTHONDONTWRITEBYTECODE=1 python checks/test_exact.py

The first two commands emit the same deterministic JSON bytes. To save a new output, supply `--output /absolute/path/outside/package/new-result.json`. The parent directory must already exist. Existing targets, symlinks/noncanonical destinations, and all destinations inside the source package are refused. Nothing is overwritten. The same interface is available for the audit harness.

The checker takes about 3–4 seconds in the build environment. The adversarial harness takes about one minute. Times are descriptive, not acceptance criteria.

`exact_results.json` is the checked finite result. `audit_results.json` records normal/optimized clean-copy replays, byte identity, selected mutations, and output-refusal tests. Neither output is read as a mathematical input by either executable.

## Exact coverage

1. **Boundary and Pfaffian identities:** n = 1,...,8 at t = 1/4, 1, 3, 7/2, 9. Kernel entries are independently formed from the bivariate generating function. Recursive Pfaffians, Gaussian-elimination determinants and solves, both cofactor parities, the complete bordered Pascal factorization, transformed forcing and the finite boundary ratio are compared. This is 40 matrix cases.
2. **Independent combinatorial cross-check:** all symmetric alternating-sign matrices of sizes 1,...,5 are enumerated by legal row and column partial sums, with symmetry enforced entrywise. Full diagonal-count distributions are checked against fixtures and the separately evaluated Pfaffian at all five t values. The total counts are 1, 2, 5, 16, 67. This is exhaustive enumeration at these sizes, not enumeration for n > 5.
3. **Full finite Hahn adjoint resolvent:** another 40 cases use unnormalized real monic bases so every square-root normalization cancels. The Meixner–Pollaczek recurrence and its Gram forms are changed into the Hahn basis; imaginary translations independently verify the finite q/r operator. The actual ordered adjoint compression, determinant quotient, boundary coefficient and calibrated ratio are checked using finite inverses only.
4. **Hahn and Christoffel identities:** degrees 0,...,12, with the lowered family also constructed through degree 14. Terminating hypergeometric polynomials are evaluated using exact arithmetic in Q(i). Divisibility, the imaginary-point evaluation, norm identities, original-variable scale and the positive inverse-quadratic mass formula are checked. Moments are generated independently from the monic Jacobi recurrence, rather than by inserting the mass formula being tested.
5. **Basis and phase:** degrees 0,...,12. Apply the exact Fourier-side differential operator iL to the continuous-Hahn polynomial and compare every coefficient with the explicit Jacobi polynomial. Both leading-sign conventions, factorial norm factors, the i^j phase and the Toeplitz shift are retained. The b0 and first Galerkin constants are checked algebraically; their integral evaluations and infinite Fourier summations are not certified by finite computation.
6. **Source algebra:** the four stated removable density poles are checked in Q(sqrt(3),i). The two affine t coefficients and the two affine y coefficients are checked exactly where applicable. A rational parametrization of the unit circle reduces the nu and rho transforms, eta inverse, calibration simplification and source subtraction to polynomial cross-products. These are exact rational-function identities, not tests at a grid of real transform points. Convergence and contour-shift justifications remain analytic arguments.
7. **Finite-section defects:** deliberately nonsymmetric synthetic rational matrices in dimensions 3, 5, 8, every cut 1,...,dimension−1, and powers 0,...,6. The directly computed defect and the correctly ordered adjoint recurrence agree in 78 update steps. A separate finite-band profile verifies the reindexing signs. Synthetic checks do not establish the DSASM column-rate hypotheses or the limit recurrence.
8. **Normalizations:** pressure cumulants through order 6; finite companion cumulants from the size-1,...,5 distributions; calibrated and s=1 fourth-power amplitude factors; the inverse ansatz's r and constant coefficients for three exact parameter sets; four finite mixed-determinant Schur identities; and Jacobi's single-edge variance for ranks 1,...,12. The inverse check treats log r as a formal variable and does not numerically verify an asymptotic remainder or an integer ceiling. The amplitude's transcendental calibration constant and Fredholm value are not numerically evaluated.

All exact scalar arithmetic uses `fractions.Fraction`, with a four-dimensional field for sqrt(3) and i where needed. Neither machine floats nor `assert` is used for validation. All failures use explicit guards that remain active under `python -O`.

## Inputs and independence

`../data/cases.json` is the closed, canonical range declaration. `../data/expected.json` contains diagonal distributions and pressure cumulant fractions. The input loader rejects unknown/missing keys, duplicate JSON keys, noncanonical fractions, booleans as integer counts, altered coverage declarations and extra data files. The data directory must contain exactly those two files. The package-wide integrity tool supplies the full package inventory; the mathematical checker only reads these data files.

Formulas were reimplemented from the report and its supplied mathematical inputs. No producer check program was imported, invoked or copied. No earlier checker output is accepted as a proof input. The small distribution fixtures are independently verified by exhaustive enumeration and the kernel/Pfaffian route; derivative fixtures are verified by exact rational differentiation.

## Adversarial scope

`test_exact.py` creates separate source copies containing `checks/` and `data/`, makes each source tree read-only, and verifies the complete byte inventory before and after execution. Normal and optimized replays must be byte-identical. It also verifies that an existing output, a destination inside the source tree, and a symlinked output are refused without changing source or target bytes.

Fifteen selected mutations are each tested in normal and optimized modes: two semantic fixture changes; unexpected/missing keys; boolean counts; a noncanonical fraction; a changed range; a duplicate key; an extra data file; a Christoffel factor; a source-pole coefficient; a basis phase; reversed adjoint ordering; a defect sign; and an amplitude power. Each must fail at its expected guard, emit no success JSON, and leave its immutable source copy unchanged. These are selected regression tests, not an exhaustive security or mutation-coverage claim.

The harness does not read `exact_results.json` or `audit_results.json` to decide mathematical correctness. Package-level immutable replays and checksums are handled separately by the report's top-level tools. Frozen earlier packages are never modified.
