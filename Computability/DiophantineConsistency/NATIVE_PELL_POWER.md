# Native first index and exponential recovery

These new arithmetic theorems use the authoritative old-z source
`SplitCertificate59.sourceRows` directly. The four coefficient ports remain
parameters throughout. They do not interpret arbitrary ports as a computation.

`NativePellFirstIndex.source_first_pair` derives a natural `r≥12` with

```
R=2r+1, tau=chi_(2XY²+1)(r+1), k=2 psi_(2XY²+1)(r+1).
```

Here `R=(c*j−V).toNat`, `X=x21`, `Y=x16*x9`, and `k=eta+zeta` in the original
31-coordinate order. The existing main-index recovery gives `c=psi_(a+2)(R)`.
The first index congruence gives `2n=R+1 (mod E)`. Growth gives `n<R`, and the
source window gives `R+1<E`; together they exclude every nonzero multiple of
`E`. Thus rank oddness is a conclusion, with no supplied parity premise.

`NativePellPower.source_X_eq_two_pow_rank` proves

```
X=2^R.
```

Its assumptions are the existing `NativePellBootstrap.PortBox`, positive
source coordinates, all22 source equations and the additional explicit
coefficient inequality `beta≥15`. This bound supplies `X≥16`. The lower
Pell-ratio estimate retains the actual factor two in `k=2 psi`: it proves
`X^r<2(Y+1)`, hence `2^R<Y`. The literal main-root row and the standard
Pell congruence then give `X=2^R (mod 4a+3)` with both representatives below
the modulus. No cubic-size exponential-decoding premise is supplied.

`NativeBinaryScale.source_q_power_radix` further derives

```
q=(2^d)^N, N>0, d*N≤R
```

when the positive width `d` satisfies the explicit relation `beta=2^d−1`.
The literal source gives `q|X`; divisors of a power of two give `q=2^u`.
The exact remainder identity for `2^u−1` modulo `2^d−1` gives `d|u`.
All conversions between signed ports and natural coordinates are proved.

`NativePellScaleBounds` also derives `3q<R` and `3u<R` from the exact rank
target and the positive old-z transport. Hence `q³|X`; the defining rows give
`N=q³`, so `q³|Y` directly. These supply the common symmetric scale required
by the subsequent half-binomial extraction, rather than assuming that scale
as an extra source hypothesis.

Dedicated checks audit all public theorem interfaces; they use only
`propext`, `Classical.choice` and `Quot.sound`. These are unbounded proofs,
not checks over sample source solutions.

The next arithmetic prerequisite is the **half-binomial** ratio extraction:
the native first coordinate is doubled, whereas the existing `Ratio90`
interface uses `k=psi`. Its undoubled conclusions cannot be reused directly.
Power/population-to-mask extraction, exact native-window decoding and its
connection to K215/refutation remain separate obligations. No object-language
ZFC derivation or fixed-payload calibration is asserted here.
