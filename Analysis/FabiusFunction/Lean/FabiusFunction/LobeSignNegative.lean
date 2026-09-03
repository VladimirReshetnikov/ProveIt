import FabiusFunction.CanonicalIntegerPoint

/-!
# The lobe-sign law on the negative axis

`LobeSignLaw` and `CanonicalIntegerPoint` prove the exponent-sequence
volume's sign law for `x > 0`.  Both quantify the lobe index over `ℕ`,
so neither says anything for `x < 0`, and the module headers record
that gap.

It is closed here, and cheaply, because `Φ_a` is **even**: every
factor `sinc(π z / 2^h)` is, so every factor of `Φ_a` is, and the
canonical real factor `1 - x²/(m+1)²` visibly is.  Reflecting `x` in
the origin therefore carries the negative axis onto the positive one
and the law transports.

The one thing to get right is the *index*.  On `-(N+1) < x < -N` the
reflected point `-x` lies in the lobe `(N, N+1)`, so the sign is
`ε_a(N)` — that is `ε_a(⌊|x|⌋)`, **not** `ε_a(⌊x⌋)`, which for
negative non-integer `x` is `⌊x⌋ = -(N+1)` and is not even a natural
number.  The volume writes the law as `sgn Φ_a(x) = ε_a(⌊x⌋)`, a form
meaningful only for `x ≥ 0`; on the negative axis the correct reading
is with `⌊|x|⌋`, and that is what is proved.

* `canonicalRealFactor_neg`, `canonicalRealProduct_neg` — evenness of
  the real canonical product;
* `generalizedRvachevProduct_neg` — evenness of `Φ_a` itself;
* `parityCharacter_mul_canonicalRealProduct_neg_pos` — **the law on a
  negative lobe**;
* `parityCharacter_mul_canonicalRealProduct_neg_natCast_pos` — and at
  a negative integer whose multiplicity vanishes.

Nothing analytic is used or claimed.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- Each canonical real factor is even in `x`: its base is
`1 - x²/(m+1)²`. -/
theorem canonicalRealFactor_neg (a : ℕ → ℕ) (x : ℝ) (m : ℕ) :
    canonicalRealFactor a (-x) m = canonicalRealFactor a x m := by
  rw [canonicalRealFactor, canonicalRealFactor, neg_sq]

/-- The real canonical product is even. -/
theorem canonicalRealProduct_neg (a : ℕ → ℕ) (x : ℝ) :
    canonicalRealProduct a (-x) = canonicalRealProduct a x := by
  rw [canonicalRealProduct, canonicalRealProduct]
  exact tprod_congr fun m => canonicalRealFactor_neg a x m

/-- **`Φ_a` is even.**  Every scale factor is, since `complexSinc`
is. -/
theorem generalizedRvachevProduct_neg (a : ℕ → ℕ) (z : ℂ) :
    generalizedRvachevProduct a (-z)
      = generalizedRvachevProduct a z := by
  rw [generalizedRvachevProduct, generalizedRvachevProduct]
  refine tprod_congr fun h => ?_
  have harg : (Real.pi : ℂ) * (-z) / (2 : ℂ) ^ h
      = -((Real.pi : ℂ) * z / (2 : ℂ) ^ h) := by
    ring
  rw [harg, complexSinc_neg]

/-- **The sign law on a negative lobe.**  For `-(N+1) < x < -N`,

`0 < ε_a(N) · Ψ_a(x)`,

with the index taken at `N = ⌊|x|⌋`.  This is the reflection of
`Fabius.parityCharacter_mul_canonicalRealProduct_pos`, and the index
is the one the reflection produces: `ε_a(⌊x⌋)` would be evaluated at a
negative integer, which the volume's digit formula does not define. -/
theorem parityCharacter_mul_canonicalRealProduct_neg_pos (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) {N : ℕ} {x : ℝ}
    (hN : x < -(N : ℝ)) (hx : -((N : ℝ) + 1) < x) :
    0 < ((parityCharacter a N : ℤ) : ℝ) *
      canonicalRealProduct a x := by
  have hlo : (N : ℝ) < -x := by linarith
  have hhi : -x < (N : ℝ) + 1 := by linarith
  have h := parityCharacter_mul_canonicalRealProduct_pos a ha hlo hhi
  rwa [canonicalRealProduct_neg] at h

/-- **The sign law at a negative integer** whose multiplicity
vanishes, the reflection of
`Fabius.parityCharacter_mul_canonicalRealProduct_natCast_pos`. -/
theorem parityCharacter_mul_canonicalRealProduct_neg_natCast_pos
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) {n : ℕ}
    (hz : weightedScaleMultiplicity 2 a n = 0) :
    0 < ((parityCharacter a n : ℤ) : ℝ) *
      canonicalRealProduct a (-(n : ℝ)) := by
  rw [canonicalRealProduct_neg]
  exact parityCharacter_mul_canonicalRealProduct_natCast_pos a ha hz

end Fabius
