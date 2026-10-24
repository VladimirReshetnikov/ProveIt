# H2082 with the whole compact54-sharp tuple

This separate candidate has **nine positive integer inputs**, **443 live
binary operations**, and **exact total degree 1,845,940**. Its nine-natural
translation has **450 operations** and the same degree. These counts are
independently recounted from the literal DAGs, with every node and every
input live. The delivered package 66 remains unchanged.

The input order is `b,g,h,s,w,C,i,j,n`. In the positive equation the absorbed
index is `j0=j-1`. In the natural equation every input except the internal
`j0` is increased by one. Intermediate registers add no variables. All
polynomial exponents are fixed natural numbers; the circuits contain only
binary addition, subtraction and multiplication. Multiplication by a fixed
scalar is charged. Fixed integer construction and reuse of a prior node
are free, as in the delivered comparison.

## What changed

The source, H2082 positions, kernel polynomials, cheap free-carrier majorant,
and shared power plan come from package 66's `H2082_simple` architecture.
All four coefficient ports are rebound together to the existing
`split116-compact/compact54-sharp` tuple. Their bit lengths are
429959/434054/429959/429960, with 215492 total raw bytes. The received gzip
payloads are preserved byte-for-byte. No individual port is mixed with the
original31 or compact44 tuple.

The 85 actual weighted kernel coefficients have absolute value strictly
below `2^864014`. All 85 generic port-box bounds are checked and listed in
`HEIGHT_CERTIFICATE.json`. There is exactly one record requiring the sharp
factorization

```
2*beta+2*beta*K0 = 2*beta*(K0+1)
 <= 2*(2^429959-1)*2^434054 < 2^864014.
```

The largest actual coefficient has 864014 bits, so this is the smallest
dyadic height exponent for this literal kernel. Set `kappa=864026`. With
maximum weight 116 and height 2082, the calibrated parameters are

```
B = 2^864026*b^2
L = b*B^2200
N = 2^6480184*B^1162
t = b*B^116.
```

For the complete two-block words `S,T`, the rank is
`R=L*(S+T+1)-S-1`, exactly as in package 66. The old original31 base
exponent was odd, giving `L=2*b*B^2200`. The new exponent is even, so the
parity factor becomes one. Removing that live doubling multiplication
changes **444 to 443 positive operations**. The threshold exponent is
recomputed from the exact population identity, rather than retaining the
old coefficient. For every binary input `b=2^k`, including `k=0`,

```
log2(L)+pop(T) = 2339*(864026+2*k)-30*k-22
              = 2*(6480184+1162*(864026+2*k))
              = 2*log2(N).
```

All 11 nonliteral fixed leaves are materialized as signed lossless
little-endian magnitudes in canonical gzip files. `fixed/BINDING.json`
records their signs, dimensions, raw hashes and compressed hashes. It also
records the two actual scale leaves, so there is no omitted fixed parameter.

## Source and degree certificates

The inert parent is exactly the old-z 31-positive source already bound in
`SplitCertificate59`. The new source applies the two invertible row shears
and the affine coordinate map

```
P_old = P_new+eta+zeta
N_old = N_new+q,     q=beta*J+1.
```

On a positive old source zero, `P_old-eta-zeta=E*(c-eta)>0` and
`N_old=q^3>q`, since `beta,J>=1`. The inverse new coordinates are therefore
positive. Conversely the displayed affine map takes every positive new
tuple to a positive old tuple, and the exact substituted rows agree.
No new transport shift or cofinality assertion is introduced. The checker
reconstructs all 22 transformed rows over 31 independent variables and
four symbolic coefficient ports. It verifies all 85 weighted records and
all 22450 degree-matched kernel/word interactions, including the forbidden
target contributions. The previous positional layout is not substituted
for this H2082 certificate.

The kernel degrees are 1627/1941/1850; the positive quadratic leader is 1.
Its unconditional dominance gaps are 25 and 455. The source bounds, sparse
+1 borrow proof, binary-population argument and unchanged free-carrier
finalizer therefore have the same ordinary arithmetic interfaces as the
reviewed package 66 construction, with the recalculated constants above.

The source/rank degrees remain `r=8799` and `nu=2324`. The exact
cancellation-resolved norm identity gives

```
degree = 104*r+400*nu+8*116+316 = 1845940
head   = 2^186 * base_scale^922760 * threshold_scale^400 > 0.
```

The checker repeats three exact sparse-polynomial defect/cancellation
identities and the strict degree comparisons. The complete universal
degree propagation is the retained ordinary proof in
`provenance/nine-PROOF.md`; the generic positive leader does not depend on
the old numerical tuple. The receipt distinguishes those identities from
the actual-coefficient modular transcription diagnostics.

## Reproduce

Python 3.10+ with its standard library is sufficient:

```
python3 replay.py
python3 -O replay.py
```

The driver authenticates the complete manifest, copies the candidate to
scratch, rebuilds every circuit and fixed leaf byte-for-byte, and runs
`verify.py` normally and with `-O`. The two mathematical receipts must
agree. Each mode checks all source identities, every coefficient bound,
literal topology/liveness/counts, 360 actual-coefficient modular output and
register comparisons, and four corruption controls. The controls alter a
kernel coefficient, restore the wrong odd-kappa block factor, alter the
threshold, and change a fixed value while preserving its proposed recipe
name. They are not merely outer manifest checks.

`build.py` is the deterministic candidate generator. `arithmetic.py` is an
attributed adaptation of the arrival-pinned package 66 builder; its exact
source hash and the small adaptations are recorded in `PROVENANCE.json`.
It is not imported by the independent verifier. The original reports and
their historical coefficient claims remain preserved as provenance.

This is an ordinary arithmetic candidate and finite certificate, with
the inherited coherent native/compiler interface explicitly retained. It
does not add a Lean proof of this new literal equation, close the native
semantic calibration, or export an object-language ZFC equivalence. The
existing checked polynomial and consistency endpoints remain separate.
