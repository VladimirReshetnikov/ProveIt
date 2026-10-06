# Report125: independent finite exact companion for A279571

## Reproduce

Python 3.9 or later, standard library only. Run from any directory:

```sh
python3 /path/to/checks/verify.py --output /tmp/a279571-leading.json
python3 -O /path/to/checks/verify.py --output /tmp/a279571-leading-O.json
python3 /path/to/checks/negative_tests.py --output /tmp/a279571-negative.json
```

Outputs must be outside this sealed `checks/` directory. The report's reference
outputs are `../data/verification_results.json` and `../data/negative_results.json`.
The checker neither accesses the network nor uses numerical fits, SymPy, NumPy,
mpmath, a compiler, or floating-point approximations. All arithmetic is exact:
integers, rational Taylor coefficients, rational polynomials, and Q(sqrt(3)).
There are no Python `assert` guards. Normal and optimized (`-O`) execution use
active explicit exceptions and produce byte-identical deterministic result JSON.
Both programs leave every source byte and inventory member unchanged, suppress
bytecode generation, and work from private clean copies as tested below.

## New leading-equivalent algebra

The new root `verify.py` does **not** call or import the producer's
`derive_correctors.py`, and does not read its output. It constructs the four
closed geometric transition transforms directly, then works in the exact
second-degree Taylor ring in `(q1,q2,t)`. The `t` variable counts every original
step; return-cycle endpoints are not substituted for original time.

It independently verifies:

- Forward and stationary-reversed color matrices, stationary law, drifts,
  mean-zero drift correctors, both conditional martingale covariances, their
  effective covariance, and both mean-zero second-order Poisson correctors
- Explicit cancellation `Gamma + P_col B - B = Sigma` in both colors and time
  directions. The conditional covariance defect is checked to be nonzero
- Joint mean and covariance of `(Z1,Z2,L)` for return cycles to **both** P and Q,
  for **both** forward and reverse walks. These are four exact transform
  computations, retaining displacement/duration cross terms. Mean duration is
  3/2 for P and 3 for Q; joint determinants are 225/32 and 225, respectively
- Spatial cycle covariance divided by **expected original duration**, stationary
  return-duration normalization, and positive joint determinants
- The exact whitening map `A=[[1,2/5],[0,sqrt(3)/5]]`, with
  `A Sigma A^T=I`, `A^T A=Sigma^{-1}`, positive Jacobian `sqrt(3)/5`, and
  `cos(theta)^2=4/7`. This is the explicit whitening used in the report
- Brownian leading heat-kernel coefficient, radial/angular integral factors,
  survival-density normalization, and the midpoint identity
  `b_theta^2 2^(p+1) I2=b_theta`, using exact Laurent monomials. The symbols are
  `H=2^(p/2), theta, Gamma(p+1), Gamma(p/2+1), p`. This checks normalization
  algebra, not the analytic heat-kernel theorem or angular uniformity
- An independent method-of-images check for wedges of angle pi/m,
  `m=1,2,3,4,6`: complete four-variable reflection-polynomial cancellation at
  every degree below m, and the degree-m coefficient. Thus these are polynomial
  identities, not sample-point comparisons. The exact `pi*b` values are
  `1,1/2,1/8,1/48,1/3840`; these special angles do not replace the model's angle
- All four coefficients in the inverse center
  `(L+kappa log L-kappa log lambda-log C_A)/lambda`, the exact residual sign
  `-kappa log(1+b(L)/L)`, and the algebraic strict margin in the stated existence
  envelope. No effective bound on the coefficient remainder is inferred
- The original `n-1` clock shift, leading counting factor `2/9`, and terminal
  stationary-color factor

The rational values in `evidence.json` are frozen claims to be checked, not a
source of derived answers: the checker reconstructs them from the transforms.
All Gamma/B values agree with the audited formulas. For example, the new P
forward return-cycle covariance is

```text
[[7/2,-5,7/8],[-5,25/2,-25/8],[7/8,-25/8,5/4]]
```

The dual negates both spatial/time cross terms; the spatial block is unchanged.

## Preserved independent finite model checks

`legacy/` is a **byte-for-byte immutable copy** of the delivered Report123
finite companion, including its original README, provenance, programs, fixtures
and manifest. Its manifest SHA-256 is

```text
79f5dfa1cb52fe41ec57b4cbc73638d502f1f9a73cec9e3af881e6fabd399295
```

The new checker validates this anchored manifest and every archived byte before
importing its verifier. The archived references to Report123 describe that
original archive context; the accompanying standalone proof for this package
is `../report125.tex`. Nothing in the earlier Report123 delivery is edited.

The new root verification reruns the archived exact functions, including:

- Direct forbidden-pattern avoidance, append-maximum injection premises, and
  **full state distributions n=0..9**
- Independent generating-tree and diagonal-prefix/row-suffix recurrences with
  matching **full state distributions and public coefficients n=0..65**
- Coordinate shift, reachable-state/domain and automatic finite-size bounds;
  both cleared functional equations and the eliminated equation through n=65
- Characteristic/kernel determinants, critical discriminant collision, Perron
  tilt, two covariance derivations, arithmetic angle premises
- All six length-3/4 return loops at minimal boundary states and representative
  translates, their reversals and exact probabilities; dual and forward seeds
- Endpoint-by-endpoint telescoping and scalar resolvent coefficients through
  **n=12**, and finite-box killed-path reversal at lengths **1..5**
- Equality of all **1001** historical public and internally generated GMP rows

See the archived README for the optional C++/GMP run through n=1000. A fresh
long-range computation is not part of this Python-only PASS.

## Public fixture provenance

The frozen external fixture is `legacy/b279571.txt`, from
[OEIS A279571](https://oeis.org/A279571), linked as
[the public b-file](https://oeis.org/A279571/b279571.txt).
Its recorded attribution is Nicholas R. Beaton, with terms 0..32 from Vaclav
Kotesovec. The original source research records retrieval on 2026-10-02 via
`https://oeis.org/A279571/b279571.txt?download=1`. The Report123 companion recorded
an independent check of the OEIS entry, definition, table link and attribution
that day, while a new raw-byte request failed with cache miss/HTTP 403.
**This companion does not claim another fresh raw-byte retrieval.**

The public raw-byte SHA-256, unchanged here, is

```text
9fa7ab4c890fd441996ad028a2bd25c9ef69904c13f1a383371023627ac37c65
```

`legacy/historical_gmp_n0_1000.txt` is an internal archived exact GMP calculation,
**not a second external source**. Its identical bytes and all 1001 coefficients
are compared; a fresh 1000-generation run is not implied. The current independent
Python recurrence is rerun through n=65. Original commands and historical result
are preserved in `legacy/historical_verification.json`.

## Adversarial coverage and integrity

The new suite has **48 selected leading-companion cases**, plus the preserved
**19 archived semantic/schema/provenance cases**. Every case runs in normal and
`-O` modes, requires exit 1, and matches one exact expected diagnostic. The suite
also verifies four clean-copy replays in total, unchanged bytes and inventories,
and equality of normal/optimized leading result bytes.

New semantic mutations cover each direction's drift, first/second correctors,
conditional and effective covariances; original-clock duration, cycle cross
terms and determinant; whitening, angle and Jacobian; each Brownian normalization;
inverse signs/envelope; and time-shift/stationary counting factors. Schema tests
include duplicate keys, nonfinite numbers, noncanonical rationals, booleans in
integer fields, unknown nested fields and weakened ranges. Provenance and
inventory tests include falsely fresh historical data, falsely certified
analytic claims, wrong source digest, changed immutable archive, unlisted files
and empty directories, symlinks, unresealed changes, and missing/duplicate manifest
entries. Semantic fixtures are rehashed in private copies before checking, so
ordinary hash failures cannot mask the intended semantic guard. The archived
suite separately replays its original semantic mutations in isolated copies.

The root manifest recursively seals every file here except itself; its bytes
are sealed by the report package's outer inventory. Source hashes detect
accidental or uncoordinated changes, not adversarial replacement of all code and
anchors. Run trusted code. The selected regressions are not an exhaustive proof
of software correctness.

## Analytic boundary

The independently audited source's recorded SHA-256 is

```text
b2c806a56c3f8b652646527d9bf1c3c62ee64046d11e36e25db243eac53e05cf
```

This digest identifies an analytic source; it is not a finite proof certificate.
The report supplies the analytic proof and literature verification. No finite
check here certifies uniform coupling or Brownian bounds, harmonic limits,
survival/meander/local-limit theorems, dominated infinite endpoint sums,
existence or numerical digits of `C_A`, correction fits, effective inverse rates,
or the arithmetic theorem used for non-D-finiteness. In particular the exact
Brownian normalization algebra must not be presented as a proof of uniform
angular limits. No fitted amplitude or fitted corrections are supplied.
