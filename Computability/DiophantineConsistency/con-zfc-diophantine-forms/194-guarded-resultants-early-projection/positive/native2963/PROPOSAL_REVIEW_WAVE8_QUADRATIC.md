# Wave 8: independent replay and quadratic-source review

This review covers packages **54, 57 and 59** placed by
`beb0192cb8dc36f78c369c080f2adfbc1887a486`. It uses their complete arrival
ZIPs from `7331974b69:docs/incoming`, extracted into scratch space. The
placed directories may omit identical inherited members, so they were not
used as substitutes for the releases. No delivered file was repaired.

All normal replays passed. No normal-policy or integrity failure was
observed. The machine-readable receipt, archive identities, log digests and
additional source comparison are in
[`data/wave8-review-54-57-59.json`](data/wave8-review-54-57-59.json).

## Reproduction

The interpreter was Python 3.12.13, with NumPy 2.3.5 and SymPy 1.14.0.
`PYTHONDONTWRITEBYTECODE=1` and `-B` kept sealed releases free of bytecode.
The release drivers for 54 and 59 make their own temporary copies. Package
57's builder was run in a separate copy of the complete extracted release.

| Package | Normal replay | Additional verification |
|---|---|---|
| 54, calibrated carry | `verify_release.py`: 382 file hashes, 100 direct source blobs, 167 retained archive-member hashes, 14 authored checks | All 7 negative controls passed; `rebuild_artifacts.py` reproduced 112 artifacts byte for byte |
| 57, separated degrees | `reproduce.py`: 54 pinned inputs and all 13 build/check stages passed | Rebuilt the complete native four-port tuple; all four compressed payloads agree. All 191 files in the rebuilt copy agree byte for byte with the pristine release |
| 59, degree separated | `verify.py`: all 25 stages passed, with 74 regenerated files byte identical and 537 sealed files checked | All 3 root integrity controls passed. The source-certificate stage also passed its 10 semantic mutation controls and compared normal/optimized source-checker output byte for byte |

The top-level drivers in **all three** packages deliberately reject `-O`.
Each rejection was independently observed with exit code 1 and its stated
policy message. These are successful rejection controls, not optimized
root-replay successes. Package 59's separate source checker supports `-O`,
as checked by its `encoding/test_split.py` stage.

The main commands were `python -B verify_release.py`,
`python -B negative_controls.py`, and `python -B rebuild_artifacts.py` for
54; `python -B reproduce.py` and
`python -B coefficients/build_coefficients.py` for 57; and
`python -B verify.py` and `python -B negative_controls.py` for 59. These
were run from the corresponding extracted roots or their separate copies.

## Relevant nine-variable comparison

These are verified finite circuit metrics on the stated domains, charging
binary addition, subtraction and multiplication. They do not assert a
global minimum or bit complexity.

| Package and point | Domain | Operations | Exact degree | Raw bytes in its whole native tuple |
|---|---|---:|---:|---:|
| 54, low-cost point | 9 positive integers | 490 | 9,461,300 | 215,492 |
| 54, recommended point | 9 positive integers | 564 | 4,400,764 | 215,492 |
| 54, lower-degree point | 9 positive integers | 598 | 4,399,820 | 215,492 |
| 57 | 9 positive integers | 499 | 2,628,944 | 295,388 |
| 57 | 9 naturals | 501 | 2,628,944 | 295,388 |
| 59, free-coordinate adjunct | 9 positive integers | 473 | 1,910,404 | 533,099 |
| 59, free-coordinate adjunct | 9 naturals | 480 | 1,910,404 | 533,099 |

Package 59's recommended adjunct improves both degree and operation count
over the other nine-positive points reviewed here. Its native coefficients
are larger. In particular, it does not dominate 54 or 57 when coefficient
storage is an objective. These byte counts concern the four native ports;
they are not totals for all derived fixed circuit leaves.

## What the finite certificates establish

**54** keeps the homogeneous quadratic coding architecture and reduces the
source burden by shifting only twelve coordinates. Its positivity proof
recovers the other nineteen coordinates from the actual equations. The
source has 109 coefficient records and 62 active monomials, compared with
136 records and 71 active monomials in the all-coordinate shift used by the
current package-52 Lean adapter. Its exhaustive certificates check the
actual supported terms against all 528 homogeneous pairs. This architecture
fits the existing `SelectiveQuadraticCoding` interface, but the selective
positivity argument and changed affine substitution need new Lean proofs.

**57** separates degrees instead of homogenizing every term with a dummy
coordinate. Its three kernels multiply `1`, the positive-coordinate word,
and its square separately. Same-degree isolation is sufficient; a linear
label may collide with a quadratic label. The replay checks all 23,599
interactions of 94 source records and reconstructs all 22 residuals as
formal polynomials in the witnesses and coefficient ports. The largest
weight is 108, the largest target is 1914, and the positive carrier is
`B^1915 * (y^2 + 1)`. That carrier proves positivity before any bound or
digit decoding of `g`. Its coherent compact tuple is rebuilt exactly.

**59** adds two invertible row operations, reducing 94 records to 89. Its
source checker independently parses the old source, checks the two inverse
row identities, enumerates 22,544 source/expansion interactions, and compares
all 22 extracted formal polynomials. The degree-separated kernels have
degrees 1719, 2027 and 1929, with largest input weight 116 and convolution
height 2161. The leading coefficient of the quadratic kernel is exactly
`+1`. Degree gaps and the lower bound on the positive-coordinate word
therefore prove positivity for every natural `g`, before digit recovery.
The optional all-real positivity repair is a separate off-target monomial.
The recommended nine-variable adjunct also incorporates the late
free-coordinate and shorter carry-block arguments.

## Exact source convention: a required bridge

Packages 57 and 59 use the same raw parent JSON, SHA-256
`1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287`.
It is not literally the current `NativeQuadraticParent` source, SHA-256
`ac2a67782d344d1e74fd93bc3f09fae0097eaed1829fd8194ae235ae84763e48`.

An independent exact sparse expansion of all 60 frozen Lean-source gates,
over all 31 witness variables and four coefficient ports, found 21 identical
rows. In the fifteenth row, the older source is

```
(K0+w)*C + (q-F) - z*(q-1) = 1,
```

whereas the package-52 source is

```
(K0+w)*C = F + z*beta*J.
```

The older residual equals the newer residual plus `beta*J`. All 22
polynomials agree after substituting `z_old = z_new + 1`. This substitution
maps positive `z_new` to `z_old > 1`; the positive boundary `z_old = 1`
cannot be discarded by an unconditional generic source bijection. The
original native interface licenses the older convention. The package-52
canonical compiler-witness argument for its shift is a distinct dependency.
Any Lean reuse must expose this boundary or formalize the older row directly.

## Recommended next foundation

Retain the checked package-52 equation as a checkpoint and use package 59's
degree-separated/free-coordinate architecture for further size work.
Required new formal components are the three-layer extraction identity,
the two invertible row operations, leading-layer positivity and sparse
padding bounds. Existing mask decoding and central carry lemmas remain
useful, with their precise range hypotheses retained.

There is also a concrete smaller-coefficient feasibility result. Replacing
the **whole** original tuple in 59 by the coherent compact tuple used in 57
gives maximum termwise majorant bit length **1,182,955** across all 89 kernel
coefficients. Thus the candidate floor `2^1182967` has the required factor
4096 and retains odd exponent parity. This was computed from every literal
kernel coefficient; the receipt records its input hash. It suggests that
the 59 architecture can use the smaller compact tuple. It does **not** yet
certify a newly instantiated circuit, an exact operation ledger, its full
source/finalizer contract, or native calibration for a new closed endpoint.

Finite replay establishes the stated exact algebraic data and reproduction
results. The inherited unbounded compiler/calibration chain and an internal
object-language ZFC consistency equivalence remain separate proof obligations.
