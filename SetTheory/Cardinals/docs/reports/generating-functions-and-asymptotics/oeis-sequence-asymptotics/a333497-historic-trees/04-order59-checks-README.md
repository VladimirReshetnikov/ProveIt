# Exact reader checks for the d=30 counterexample

Python 3.10 or later; standard library only. No installation, network access,
floating-point arithmetic, root-finding, private research notes, or source-paper
copies are required. Tested with Python 3.12.

From this directory:

```sh
python -B check.py
python -B -O check.py
python -B validate_bundle.py --output /tmp/report117-validation.json
```

Exit 0 means PASS, 1 a named check failure, and 2 an unexpected exception.
Every substantive guard is an explicit conditional, not an `assert`, and
therefore remains active under `-O`. JSON outputs distinguish FAIL from ERROR;
an unexpected exception never counts as a successful negative test.
`--skip-integrity` on `check.py` is a development option, not verification of a
sealed distribution. Output files must be outside this checks directory.

## What is checked

The fixture uses derivative order d=30, paper parameter m=29, and ordinary
B-tree order 59. These are distinct, fixed fields. Its coordinate and product
endpoints are also fixed, preventing an off-by-one input from silently testing
a different model.

For A=30·31···59, q=911/100, R+iI=product(100a+911i), and S=100^30 A,
the checker reconstructs and verifies these seven strict conditions:

1. R>0
2. I>0
3. R²+I²<4S²
4. sum[q/a−(q/a)^3/3]>6
5. sum(q/a)<7
6. product(a²+100)>4A²
7. sum(10/a)<8

Every sum and product here ranges over integers 30≤a≤59. Gaussian integer
multiplication is cross-checked by evaluating the independently represented
polynomial product(a+x) at x=iq with rational arithmetic. The integer A,
normalizer S, all seven quantities, and both phase inputs are compared with
canonical exact fixture values, not accepted from a table of booleans.
The report's illustrative bounds 1.994<R/S<1.995 and
0.0049<I/S<0.0050 are checked as rational inequalities too.

The checker independently expands det(lambda I−B) using its two nonzero
permutation terms and compares it with product(lambda+a)−2A. It verifies the
exact roots 1 and −90 and their nonzero derivatives; division by lambda−1;
all 30 polynomial eigenvector identities, including the final closure;
the positive and alternating real eigenvectors; and the paper's factorial
coefficient prefactor. Sample coefficient-index identities use n=0,1,2,10,100.
The polynomial identities are full coefficient comparisons, not numerical
sampling of roots. Those checks use only integers and Fraction.

An additional ordinary, unscaled rational Routh table for the degree-29
quotient has 28 positive first-column entries, one negative, then one positive.
Every pivot and row is nonzero. By the Routh theorem the quotient has two
right-half-plane roots, 27 left-half-plane roots, and no imaginary-axis roots.
Adding the factored root 1 yields 3 right, 27 left, and 0 axis roots. This
independent route corroborates the compact phase certificate. The Routh theorem,
like the analytic phase-curve argument, is a mathematical theorem used in the
interpretation; the program does not implement a formal proof assistant.

The seven inequalities, the elementary bound 3<pi<22/7, the arctangent bounds,
and the report's strictly decreasing phase along the modulus curve identify
exactly winding index 1 as the unstable nonreal pair. Stable pairs have indices
2 through 14. The code checks the rational comparisons and index bookkeeping;
it does not substitute finite sampling for the analytic phase-curve proof.

The closed cyclic cone, its invariance, the exclusion of the entire stable
subspace, stable-manifold tangency, and coefficient-to-function Abelian
implication remain analytic arguments in the report. This suite does not
certify the actual replacement asymptotic, a periodic attractor, the first
integer transition, any classification outside d=30, or literature priority.

## Strict schemas, integrity, and replay

`fixtures/certificate.json` has a closed schema at every object level. All
integer-valued JSON fields reject booleans. Large exact numbers are bounded,
canonical strings; unreduced rationals, floats, nonfinite values, duplicate
keys, missing fields, unexpected fields, and incorrect array lengths fail.
The derivative order is locked before any size-dependent computation.

`MANIFEST.json` seals every ordinary file in this directory except itself.
There are no cache exclusions: unlisted `__pycache__` files fail. Run with
`-B`; the harness also disables bytecode generation before importing local
code. Missing, changed, or unlisted files; unsafe manifest paths; symlinks;
and special files are rejected. Input files are limited to 256 KiB and the
checks directory to 32 files. The manifest detects modification, but is not
an authenticity signature against someone replacing both checks and data.

`validate_bundle.py` compares normal and optimized results, reruns both in a
fresh temporary directory, and records source hashes before and after. It
mutates every fixture scalar and every array entry individually. These
semantic mutations reseal the temporary manifest so failures must come from
schema/algebra checks. Separate strict-boundary mutations reach each of the
seven inequality guards. Schema and inventory mutations also test malformed
JSON, boolean/integer confusion, off-by-one indexing, bad fractions, duplicate
keys, missing files, unlisted bytecode, symlinks, and FIFOs. Every mutation must
produce its exact named failure in both normal and optimized mode. Each child
process has a 15-second limit; the entire replay has a 180-second limit.

For the enclosing report package:

```sh
python -B check_manifest.py ..
```

The publisher uses `--write` only after all package files are final. Readers
should verify rather than rewrite `CHECKSUMS.sha256`. That package inventory
includes every file except the checksum file itself, without cache exclusions.
Ten independent package-manifest mutations are tested in both Python modes.
