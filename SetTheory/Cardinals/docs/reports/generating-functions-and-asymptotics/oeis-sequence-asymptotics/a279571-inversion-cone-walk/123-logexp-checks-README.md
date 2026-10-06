# A279571 independent exact finite-check companion

## Run

Python 3.9 or later, standard library only. No SymPy, NumPy, mpmath, compiler,
network request, or fitted asymptotic constant is used in the authoritative
checks. Run from any working directory:

```sh
python3 /path/to/checks/verify.py --output /tmp/a279571-verification.json
python3 -O /path/to/checks/verify.py --output /tmp/a279571-optimized.json
python3 /path/to/checks/negative_tests.py --output /tmp/a279571-negative.json
```

`--output` is optional. Output paths must resolve outside this sealed directory.
A successful run prints `PASS` lines and exits 0. A failed guard prints a
specific `FAIL: ...` diagnostic and exits 1. No check relies on Python's
`assert`, so `-O` does not remove any guard. Output JSON is deterministic for
these source bytes. Running the scripts does not change source bytes or add
bytecode files. The negative suite automatically repeats clean-copy replay and
all its negative cases in both interpreter modes. In the surrounding report
package, the two authoritative result files are under `data/`.

## What is checked

- All named files, no unexpected members, no directories or symlinks inside
  `checks/`, a strict closed SHA-256 inventory, duplicate-free JSON, exact
  schemas, canonical rational strings (reduced numerator/positive denominator,
  no `-0` or redundant `/1`), and integer-versus-boolean field types
- Direct original forbidden-pattern extension for inversion sequences and full
  `(n-h,k,color)` state distributions through **n=9**, not just total counts;
  appending the maximum is checked as an injection premise on every enumerated
  object
- A direct-transition generating-tree DP and an independently solved
  diagonal-prefix/row-suffix recurrence have identical **full state
  distributions n=0..65**; their totals equal the frozen external b-file over
  that range; label/domain and automatic size bounds are checked
- Both cleared functional equations and the eliminated `K(P+Q)` equation at
  every coefficient **z^0..z^65**, using sparse exact polynomials
- Exact symbolic characteristic/kernel determinants, quadratic coefficients,
  discriminant factorization, critical double-root collision, and the affine
  transport coefficient, using an independent small rational-polynomial engine
- Perron critical point, positive right vector, second eigenvalue, individual
  edge tilts, color transition matrix, positive stationary law, zero drift and
  geometric-tail parameters
- Effective covariance by the implicit log-Perron Hessian and, independently,
  closed geometric sums of corrected martingale increments; determinant,
  negative off-diagonal sign, and angle ratio are retained exactly
- The reversed process's drifts, mean-zero corrector, Poisson equation and
  effective covariance are calculated independently from the reversed edge
  families; detailed balance of finite-box killed paths of lengths **1..5** is
  checked on `[0,3]^2 x {P,Q}`. This is a finite path-reversal identity, not a
  numerical approximation of an infinite reverse transition sum
- Every one of the **six length-3/4 return-loop templates** at its minimal
  boundary state, all intermediate domain constraints, exact loop probability
  `9^(-length)`, reversed loops, and representative nonnegative translates
- The four-edge dual seed, its indefinitely repeatable `(1,1)` advance, forward
  diagonal seed, first-step measure, endpoint-by-endpoint telescoping count
  identities through **n=12**, and scalar resolvent coefficients through n=12
- Exact finite premises for the irrationality argument: `cos(theta)^2=4/7`,
  `cos(2theta)=1/7`, `2cos(2theta)=2/7` is a rational noninteger, and the exact
  comparisons implying `4<p<5`; the two formal leading-log inverse coefficient
  cancellations are checked
- All **1001 archived external coefficients** equal the separately identified
  internally generated historical GMP output; both raw-byte hashes are checked

The supported theorem is a logarithmic law, `a_n=9^n n^(-kappa+o(1))`, with
`kappa=1+pi/arccos(2/sqrt(7))`. The finite computation does **not** prove that
law, a limiting amplitude, a complete expansion, the FCLT/LLT, annulus transfer,
interior bridge estimates, dominant-circle continuation, G-function theorem,
or non-D-finiteness. Those are analytic/arithmetic arguments in the report and
its independently audited source. In particular no fitted amplitude or
correction table is included as default reader evidence. The formal inverse
cancellation does not itself justify an asymptotic inversion or a bounded
inverse constant.

## Source provenance and limits

The public table is attributed by [OEIS A279571](https://oeis.org/A279571) to
Nicholas R. Beaton, with terms 0..32 from Vaclav Kotesovec. Its linked URL is
[the b-file](https://oeis.org/A279571/b279571.txt). The source research package
records retrieval on 2026-10-02 via the same URL with `?download=1`.

This companion independently checked the OEIS entry, definition, table link
and attribution on 2026-10-02. A new raw-byte fetch failed with a web cache miss
and HTTP 403, so **fresh raw-byte re-retrieval is not claimed**. This archive
uses the frozen external file from the source research package, whose raw
SHA-256 is:

```text
9fa7ab4c890fd441996ad028a2bd25c9ef69904c13f1a383371023627ac37c65
```

The identical bytes in `historical_gmp_n0_1000.txt` are a historical internal
calculation, **not a second external source**. The current check reads and
compares all its coefficients but does not silently claim to have rerun that
1000-generation calculation. `historical_verification.json` preserves the
original recorded algorithm, original filenames/commands and result.
`provenance.json` fixes these roles and refers to the accompanying
`../report123.tex` for the analytic arguments. Its bytes are sealed by the
surrounding report's outer inventory; this directory does not mechanically
verify those arguments. The source theorem tree is from
Britt and Beaton, [arXiv:2512.21943v3, section 2.5](https://arxiv.org/html/2512.21943v3#S2.SS5).

## Optional fresh long-range GMP reproduction

This is optional and **not** part of the default Python-only PASS. It needs a
C++17 compiler and GMP C++ development headers/libraries. `enumerate_gmp.cpp`
is the archived exact prefix/suffix implementation, copied without alteration.
It uses O(N^3) integer additions and O(N^2) growing-integer storage. The n=1000
run can be much slower and larger than the modest-range authoritative checker.
Place every output outside this directory:

```sh
g++ -O3 -std=c++17 /path/to/checks/enumerate_gmp.cpp -lgmpxx -lgmp -o /tmp/a279571-enumerate
/tmp/a279571-enumerate 1000 > /tmp/a279571-fresh-gmp.txt
cmp /tmp/a279571-fresh-gmp.txt /path/to/checks/b279571.txt
sha256sum /tmp/a279571-fresh-gmp.txt
```

The archived source accepts a nonnegative decimal generation bound as its
single positional argument. Use the documented valid value `1000`; it is a
small archival research program, not a hardened general-purpose CLI. A
successful `cmp` after a fresh run establishes a fresh 1001-coefficient
comparison. The independent Python recurrence is authoritative through n=65
without this optional dependency.

## Adversarial tests and integrity scope

`negative_tests.py` makes private temporary copies and, for semantic mutations,
recomputes their manifests before invoking the checker. This prevents a hash
failure from masking the guard being tested. Nineteen selected cases cover a
wrong covariance cross term, mean-zero but wrong forward/reverse correctors,
wrong critical point/Perron vector, nonreturning loop, wrong dual seed endpoint,
wrong first-step measure, inverse/log-angle corruption, noncanonical rational,
boolean-as-integer, weakened coverage, unknown nested field, duplicate key,
historical data falsely relabeled as external, changed public coefficient,
unlisted payload and an unresealed change. Every case must fail with its exact
expected diagnostic in both normal and `-O` modes. This is a selected regression
suite, not an exhaustive software correctness proof.

`manifest.sha256` seals every other regular file here. It cannot self-hash; the
surrounding report's outer inventory seals it. Hashes detect accidental or
uncoordinated change, not coordinated replacement of code and its manifest by
an adversary. Run only trusted copies. No sealed earlier report is altered by
this companion.
