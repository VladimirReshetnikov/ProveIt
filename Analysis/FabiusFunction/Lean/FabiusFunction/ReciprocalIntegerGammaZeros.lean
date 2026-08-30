import FabiusFunction.DyadicGammaOrder

/-!
# The zero set of the geometric reciprocal Gamma at reciprocal-integer base

`GeometricReciprocalGamma` describes the zeros of

`G_q(z) = ∏_h Γ(1 + q^h z)⁻¹`

in the *affine* form `∃ n m, 1 + q^n z = -m`, which is the shape that
is safe at `q = 0`, where no scale can be divided out.  At
`q = 1/b` with an integer base `b ≥ 2` the description collapses to an
arithmetic one: the zeros are exactly the strictly negative integers,
independently of `b`.

`DyadicGammaOrder` proves this at `b = 2`
(`dyadicReciprocalGamma_eq_zero_iff`).  The same argument works at any
integer base, and the representations volume needs it: it states the
pole of `Γ_geom` at `-n` to have order `1 + max{h : b^h ∣ n}` for
every integer `b ≥ 2`, and records that "the general integer-base
pole-order formula" is not formalized — "only the dyadic order has an
exact counterpart".

This module supplies the *set* at every integer base.  The **order**
is not proved here and is not a corollary of it: at `b = 2` the order
comes from transferring the integer-zero order of the Rvachev product
through `G₂(z) G₂(-z) = Φ(z)`, and the corpus has no `Φ_b` to transfer
through at other bases.  Proving it directly would mean splitting off
the finitely many vanishing factors — the `h` with `b^h ∣ n` — and
showing the remaining product is an analytic unit, which is the
architecture of `FabiusFunction.CanonicalIntegerPoint` and
`FabiusFunction.GeneralizedRvachevEntire` applied to a different
family.  The arithmetic side of that count is already available at
arbitrary base as `Fabius.weightedScaleMultiplicity b (fun _ => 1)`.

* `Fabius.norm_inv_natCast_lt_one` — `‖1/b‖ < 1` for `b ≥ 2`;
* `Fabius.geometricReciprocalGamma_inv_natCast_eq_zero_iff` — **the
  zero set**: exactly the strictly negative integers, at every
  integer base `b ≥ 2`;
* `Fabius.geometricReciprocalGamma_inv_natCast_ne_zero_of_nonneg` —
  hence no zero at a nonnegative integer;
* `Fabius.geometricGamma_inv_natCast_meromorphic` — the Gamma side is
  meromorphic at every such base.
-/

set_option autoImplicit false

namespace Fabius

/-- For an integer base `b ≥ 2` the ratio `1/b` lies strictly inside
the unit disc, which is the hypothesis every geometric statement
carries. -/
theorem norm_inv_natCast_lt_one {b : ℕ} (hb : 2 ≤ b) :
    ‖((b : ℂ))⁻¹‖ < 1 := by
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < (b : ℝ) := by linarith
  have hbne : ((b : ℂ)) ≠ 0 := by
    have : (b : ℝ) ≠ 0 := ne_of_gt hbpos
    exact_mod_cast this
  rw [norm_inv, Complex.norm_natCast]
  rw [inv_lt_one_iff₀]
  right
  linarith

/-- **The zero set at reciprocal-integer base.**  For every integer
`b ≥ 2`,

`G_{1/b}(z) = 0 ↔ z` is a strictly negative integer,

independently of `b`.  The affine description
`∃ n m, 1 + q^n z = -m` becomes `z = -(m+1) b^n`, and `(m+1) b^n`
ranges over exactly the positive integers as `n` and `m` range over
`ℕ` — surjectively already at `n = 0`. -/
theorem geometricReciprocalGamma_inv_natCast_eq_zero_iff {b : ℕ}
    (hb : 2 ≤ b) (z : ℂ) :
    geometricReciprocalGamma ((b : ℂ))⁻¹ z = 0 ↔
      ∃ N : ℕ, N ≠ 0 ∧ z = -(N : ℂ) := by
  have hbne : ((b : ℂ)) ≠ 0 := by
    have hb0 : b ≠ 0 := by omega
    exact_mod_cast hb0
  rw [geometricReciprocalGamma_eq_zero_iff _ z (norm_inv_natCast_lt_one hb)]
  constructor
  · rintro ⟨n, m, hnm⟩
    refine ⟨(m + 1) * b ^ n, by positivity, ?_⟩
    have hpow : ((b : ℂ)) ^ n ≠ 0 := pow_ne_zero n hbne
    have hz : (((b : ℂ))⁻¹) ^ n * z = -((m + 1 : ℕ) : ℂ) := by
      push_cast
      push_cast at hnm
      linear_combination hnm
    have hmul : z = ((b : ℂ)) ^ n * ((((b : ℂ))⁻¹) ^ n * z) := by
      rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hbne, one_pow, one_mul]
    rw [hmul, hz]
    push_cast
    ring
  · rintro ⟨N, hN, rfl⟩
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, N = m + 1 := ⟨N - 1, by omega⟩
    refine ⟨0, m, ?_⟩
    push_cast
    ring

/-- No zero at a nonnegative integer: the zeros are strictly
negative. -/
theorem geometricReciprocalGamma_inv_natCast_ne_zero_of_nonneg {b : ℕ}
    (hb : 2 ≤ b) (n : ℕ) :
    geometricReciprocalGamma ((b : ℂ))⁻¹ (n : ℂ) ≠ 0 := by
  intro hzero
  obtain ⟨N, hN, hz⟩ :=
    (geometricReciprocalGamma_inv_natCast_eq_zero_iff hb _).mp hzero
  have hposN : 0 < N := Nat.pos_of_ne_zero hN
  have hreal : (n : ℝ) = -(N : ℝ) := by exact_mod_cast congrArg Complex.re hz
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hposN
  linarith

/-- The Gamma side is meromorphic at every reciprocal-integer base,
the base-`b` form of `Fabius.dyadicGamma_meromorphic`. -/
theorem geometricGamma_inv_natCast_meromorphic {b : ℕ} (hb : 2 ≤ b) :
    Meromorphic (geometricGamma ((b : ℂ))⁻¹) :=
  geometricGamma_meromorphic _ (norm_inv_natCast_lt_one hb)

end Fabius
