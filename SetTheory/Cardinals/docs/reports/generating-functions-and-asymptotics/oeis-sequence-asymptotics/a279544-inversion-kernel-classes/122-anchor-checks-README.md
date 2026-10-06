# Exact reproducibility companion for report122

Run from any working directory:

    python -B checks/verify.py --output /absolute/external/report122-results.json
    python -B checks/negative_tests.py --output /absolute/external/report122-negative.json

No network or non-standard package is needed. Python 3.10 or newer is required.
The verifier is also valid with `python -B -O`; every guard is an explicit check.
Outputs must be outside the package. Bytecode creation is disabled. `inventory.json`
lists the complete allowed contents of this subtree and their SHA-256 hashes;
unlisted files, directories and symlinks are rejected. This is an integrity check,
not a cryptographic signature or a trust boundary against a replaced verifier.

`certificate.json` uses a strict, duplicate-key-rejecting schema. Rational strings
are reduced numerator/positive-denominator pairs, including integers as `n/1`.
No decimal floating-point value is used in a mathematical certificate.

`exact_model.py` independently implements rank-pattern avoidance, range-difference
propagation of the transformed tree, full cleared source functional equations,
the scalar kernel identity, and generic rational formal-series operations.
The model range is n=0..150; direct enumeration and full state distributions are
compared for n=0..9; the 26 published terms are compared at n=0..25; functional
and scalar identities through z^40; root/anchor identities through z^64; and
finite-orbit quotients for m=0..30 through n=m+1. Generated terms beyond n=25
are internally reproduced, not compared with an external b-file.

`exact_analytic.py` reimplements the audited producer's directed integer-lattice,
interval-jet and complex-rectangle formulas. The analytic certificate is a
reproducible exact calculation based on the report's proved estimates, not an
independent formal proof. It checks the normal-convergence domain, zero-free
denominator bounds, complex-orbit tails, derivative Cauchy remainder and
coefficient Cauchy remainders, and recomputes C, d1 and d2. Provenance hashes
identify the exact producer snapshots; these raw source files are not delivered
here. The Puiseux root equation is checked independently in Q(sqrt(3)) through
t^6. Sparse symbolic algebra also checks the inverse expansion through L^-2
(including P2) and the stated first transfer factors. Holomorphic continuation, transfer theorems, all-order expansions and inverse
localization remain mathematical arguments in the report; finite checks alone
do not establish them. Previously published amplitude digits are credited there.

All results are deterministic JSON, including complete rational interval endpoints,
state/sequence hashes, exact tested ranges and negative-test diagnostics. Normal,
optimized and clean-copy replay results are intended to match byte-for-byte.

## Checked counts and negative cases

The direct enumerator tests 41,342 candidate extensions. Full state counts for
n=0..9 are 1, 1, 2, 4, 8, 14, 22, 32, 44, 58. The source equation inputs contain
10,701 S monomials and 9,139 T monomials through degree 40; the scalar H input
contains 821 monomials. All residuals are zero. There are 31 finite quotient tests.
The first discrepancy is 1 at m=0 and 1/2 at m=1..30; no exact finite quotient
identity beyond its proved degree is claimed.

The mutation suite has 29 cases in each interpreter mode, 58 executions total.
Cases exercise malformed/duplicate/extra schema data, canonical rationals and
integers, boolean rejection, wrong finite ranges, root/critical domain, orbit
contraction, global disk invariance and denominator floor, three tail bounds,
Puiseux root coefficients, published/generated terms, the all-zero functional
correction, finite-orbit discrepancy, amplitude and correction intervals,
closed inventory, symlink/directory/digest/missing-file rejection, and forbidden
internal output. Each case must fail with its intended diagnostic and produce
no result file. Copies are resealed when a test must reach the mathematical
checks; deliberately unsealed copies separately test integrity enforcement.
