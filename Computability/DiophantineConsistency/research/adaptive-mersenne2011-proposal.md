# Adaptive Mersenne factor-three exclusion and binary base recovery

2026-10-26. Proposed new files only:
`NativeAdaptiveMersenne.lean` and `NativeAdaptiveMersenneChecks.lean` in
`Lean/DiophantineConsistency`, importing only the frozen
`DiophantineConsistency.NativeAdaptivePowerRecovery`.
No compiler has been invoked for this proposal. The four accepted power
sources, actual equation, coefficients and earlier receipts remain unchanged.

## Precise arithmetic checkpoint

Use integer bases and natural exponents. The first generic interface is

```lean
mersenne_not_dvd_three_power {d u : ℕ} (hd : 4 ≤ d) :
  ¬ ((2 : ℤ)^d - 1) ∣ (3*(2 : ℤ)^u - 1)
```

Let `β=2^d−1`, `r=u%d`, `t=u/d`. Since `d>0`, `r<d` and
`u=d*t+r`. The geometric-sum divisibility
`β ∣ (2^d)^t−1` gives `β ∣ 2^u−2^r`, hence divisibility of
`3*2^u−1` would imply divisibility of `3*2^r−1`.

* If `r≤d−2`, set `a=2^(d−2)`. Then `2^r≤a`, `2^d=4a`, and
  `0<3*2^r−1≤3a−1<4a−1=β`. The positive smaller multiple is impossible.
* The remaining case is `r=d−1`. Subtracting β leaves exactly
  `(3*2^r−1)−β=2^r`. This lies strictly between zero and β because
  `r≥3` and `β=2*2^r−1`.

These cases include `r=0`; no residue `1`, parity or coprimality assumption is
hidden. Integer subtraction avoids a truncated-subtraction ambiguity. The
modular reduction will be an explicit divisibility identity, not an assumed
multiplicative order.

The combined generic recovery theorem is planned as

```lean
mersenne_base_recovery {d R : ℕ} {q : ℤ}
    (hd : 4 ≤ d) (hq : 1 < q)
    (hres : (2 : ℤ)^d - 1 ∣ q - 1)
    (hdiv : q ∣ 3*(2 : ℤ)^R) :
  ¬ (3 : ℤ) ∣ q ∧ q ∣ (2 : ℤ)^R ∧
    ∃ u : ℕ, 0 < u ∧ u ≤ R ∧ q = (2 : ℤ)^u ∧ d ∣ u
```

If `3∣q`, write `q=3*m`; positivity of q implies `m>0`.
Cancel the literal nonzero factor `3` from `q∣3*2^R`, giving `m∣2^R`.
Cast the positive m to a natural and apply `Nat.dvd_prime_pow
Nat.prime_two` to obtain `m=2^u`, including the possible `u=0`.
Then `hres` contradicts `mersenne_not_dvd_three_power`. No cancellation
between q and 3 occurs before this contradiction.

Now use the already accepted `NativeAdaptiveFactorThree.bezout_three`:
`a*q+b*3=1`. Multiplying by `2^R` and using `hdiv` gives `q∣2^R`
with an explicit integer witness. The same prime-power divisor theorem
classifies positive q as `2^u` with `u≤R`; `q>1` excludes `u=0`.

The final width statement is coherent in this leaf. Cast `hres` after
`q=2^u` to `2^d−1∣2^u−1` in naturals, then use
`Nat.pow_sub_one_mod_pow_sub_one` to obtain `2^(u%d)−1=0`.
For a positive remainder the power is at least 2, a contradiction;
therefore `d∣u`. This is the same short generic argument already present
in `NativeBinaryScale.width_dvd_exponent`, whose full source was read.
That module is a proof guide, not a new import: its unrelated source-row
and `NativePellPower` dependencies are unnecessary here.

A useful generic corollary packages `u=d*N`:

```lean
mersenne_radix_recovery {d R : ℕ} {q : ℤ}
    (hd : 4 ≤ d) (hq : 1 < q)
    (hres : (2 : ℤ)^d - 1 ∣ q - 1)
    (hdiv : q ∣ 3*(2 : ℤ)^R) :
  ¬ (3 : ℤ) ∣ q ∧ q ∣ (2 : ℤ)^R ∧
    ∃ N : ℕ, 0 < N ∧ q = ((2 : ℤ)^d)^N ∧ d*N ≤ R
```

The absence of q-divisibility by 3 is a *new conclusion after* Mersenne
specialization. Earlier signed carrier lemmas correctly allowed `3∣q`.

## Binding the actual adaptive tuple

The public `adaptive_q_power_radix` takes the exact positive variables and
literal equations of `NativeAdaptivePowerRecovery.adaptive_X_eq_two_pow`,
with these two width hypotheses replacing its scalar `hbeta`:

```lean
{d : ℕ} (hd : 4 ≤ d) (hwidth : ports 0 = (2 : ℤ)^d - 1)
```

Explicitly it retains `PortBox ports`; positivity of
`J,F,alpha,X,Y,eta,zeta,gamma,r,f,i,T,u`; and

```
k = eta+zeta
q = ports 0*J+1
R = target q F alpha J (ports 2) (ports 3)
Bt = (q*ports 1+X)*(q-F-alpha)-q*F
firstA0 q (X*k*Y^2) k r Y Bt = 0
mainA1 q X Y k eta gamma (k-R-1) = 0
strongFactor (Y*(X+1)) (k*Y+eta) f i = 1
auxiliaryFactor (Y*(X+1)) (k*Y+eta) f T R u = 1.
```

From `d≥4` derive `15≤ports 0`; positive J then gives `q≥16`.
The frozen power wrapper supplies `X=2^R.toNat` and `q∣3*X` from those
literal inputs, rather than receiving either as a premise.
The definition of q supplies `β∣q−1` with quotient J. Applying the generic
recovery to exponent `R.toNat` gives the proposed conclusion

```
X = (2:ℤ)^R.toNat ∧ ¬(3:ℤ)∣q ∧ q∣X ∧
∃ N:ℕ, 0<N ∧ q=((2:ℤ)^d)^N ∧ d*N≤R.toNat.
```

A current-width specialization fixes **d=47*2011=94517** and retains the
literal coefficient hypothesis `ports 0=(2:ℤ)^(47*2011)-1` and the same
other inputs. It imports no historical compact44 tuple and no large current
kernel module; it is an exact width specialization of the arbitrary-PortBox
arithmetic theorem, not a fresh proof of the current four-port constants.
MF remains the already once-shifted `ports 3` throughout.

There is no supplied restored source, oddness/index equation, q|X, q power,
canonical witness or whole-graph-zero premise. Source reconstruction,
canonical completeness, the whole small-equation graph, metrics and internal
HA/PA equivalence are outside this checkpoint.

## Read APIs and exact cache delta

Actual source contracts read: the entire accepted PowerRecovery and
NativeBinaryScale sources; `sub_one_dvd_pow_sub_one` and
`pow_one_sub_dvd_pow_mul_sub_one` in `Mathlib.Algebra.Ring.GeomSum`;
`Nat.dvd_prime_pow` in `Mathlib.Data.Nat.Prime.Basic`;
`Nat.pow_sub_one_mod_pow_sub_one` in `Mathlib.Data.Nat.GCD.Basic`;
`Int.dvd_of_mul_dvd_mul_left` in core `Init/Data/Int/DivMod/Lemmas`;
and the accepted signed `bezout_three` source. All are available through
existing imports. Header inspection found the prime/GCD APIs below
`Mathlib.NumberTheory.PellMatiyasevic`, and geometric sums below the already
imported `Mathlib.Data.Nat.Choose.Lucas` path. No external boundary is added.

The root-accepted power provider is
`/tmp/native-adaptive-power-root-hgpurypn/lib`, with root record SHA256
`9473432e98100b64f511acd679717a4ada8ccf4089d9ecfa206b40f66d51f495`.
Its two main objects add to the previous 30-custom inventory, giving
**32 cached custom modules, 22 external names, 66 external companions,
and two proposed fresh leaves**. No Foundation or dependency compilation
is proposed. The read-only audit rehashed all selected source/object pairs,
external source/companions and inherited provider pins and checked selected
import headers. Audit SHA256:
`235165731675608064bfc92aa916b45cfecb6981016e9e3b6cf213a0673b9c3e`
at `adaptive-mersenne2011-cache-audit.json`.

Focused checks should cover the `r=0` and `r=d−1` cases at d=4,
the permitted `u=0` in the first contradiction, the necessary q>1 boundary,
the actual-width wrapper, positive cell count and exponent bound, and all
principal axiom reports. On approval, fully read source/checks/driver precede
private sequential Lean4.32 builds with `-M6000 -j1 -DElab.async=false`,
regular fresh output files and a 512 MiB reserve guard. Every failed attempt
will be retained; accepted sources/objects and Git remain untouched.
