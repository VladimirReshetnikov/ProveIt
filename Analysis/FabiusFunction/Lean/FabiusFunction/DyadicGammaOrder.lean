import FabiusFunction.GeometricReciprocalGamma

/-!
# Exact zero and pole orders for the dyadic Gamma product

The reciprocal dyadic Gamma product from `GeometricReciprocalGamma` satisfies

`G₂(z) G₂(-z) = Φ(z)`,

where `Φ` is the Rvachev Fourier product.  At a negative integer `m`, the
reflected factor `G₂(-m)` is an analytic unit.  The exact integer-zero order
of `Φ` therefore transfers directly to `G₂`; inversion turns that zero into
the corresponding pole of the meromorphic dyadic Gamma function.

This file also simplifies the generic affine zero-orbit description to the
statement that the dyadic reciprocal product vanishes exactly at the negative
integers.
-/

set_option autoImplicit false

namespace Fabius

noncomputable section

/-- The zeros of the reciprocal dyadic Gamma product are exactly the strictly
negative integers. -/
theorem dyadicReciprocalGamma_eq_zero_iff (z : ℂ) :
    dyadicReciprocalGamma z = 0 ↔
      ∃ m : ℕ, m ≠ 0 ∧ z = -(m : ℂ) := by
  constructor
  · intro hz
    obtain ⟨n, m, hm⟩ :=
      (geometricReciprocalGamma_eq_zero_iff
        ((2 : ℂ)⁻¹) z (by norm_num)).mp
        (by simpa only [dyadicReciprocalGamma] using hz)
    refine ⟨(m + 1) * 2 ^ n, by positivity, ?_⟩
    have hscaled :
        ((2 : ℂ)⁻¹) ^ n * z = -((m + 1 : ℕ) : ℂ) := by
      push_cast
      linear_combination hm
    calc
      z = (2 : ℂ) ^ n * (((2 : ℂ)⁻¹) ^ n * z) := by
        rw [← mul_assoc, ← mul_pow]
        norm_num
      _ = (2 : ℂ) ^ n * -((m + 1 : ℕ) : ℂ) := by rw [hscaled]
      _ = -(((m + 1) * 2 ^ n : ℕ) : ℂ) := by
        push_cast
        ring
  · rintro ⟨m, hm, rfl⟩
    rw [dyadicReciprocalGamma]
    apply (geometricReciprocalGamma_eq_zero_iff
      ((2 : ℂ)⁻¹) (-(m : ℂ)) (by norm_num)).mpr
    refine ⟨0, m - 1, ?_⟩
    have hm1 : 1 ≤ m := by omega
    simp only [pow_zero, one_mul]
    rw [Nat.cast_sub hm1]
    push_cast
    ring

/-- The reciprocal dyadic Gamma product is nonzero at every nonnegative
integer. -/
theorem dyadicReciprocalGamma_int_ne_zero_of_nonneg
    (m : ℤ) (hm : 0 ≤ m) :
    dyadicReciprocalGamma (m : ℂ) ≠ 0 := by
  intro hzero
  obtain ⟨n, hn, heq⟩ :=
    (dyadicReciprocalGamma_eq_zero_iff (m : ℂ)).mp hzero
  have heqZ : m = -(n : ℤ) := by
    exact_mod_cast heq
  omega

/-- The reciprocal dyadic Gamma product is nonzero at every natural number. -/
theorem dyadicReciprocalGamma_nat_ne_zero (n : ℕ) :
    dyadicReciprocalGamma (n : ℂ) ≠ 0 := by
  simpa only [Int.cast_natCast] using
    dyadicReciprocalGamma_int_ne_zero_of_nonneg (n : ℤ) (by omega)

/-- The dyadic Gamma function is meromorphic on the complex plane. -/
theorem dyadicGamma_meromorphic :
    Meromorphic dyadicGamma := by
  change Meromorphic (geometricGamma ((2 : ℂ)⁻¹))
  exact geometricGamma_meromorphic ((2 : ℂ)⁻¹) (by norm_num)

/-- The reciprocal dyadic Gamma product has zero order
`1 + padicValNat 2 |m|` at every negative integer `m`. -/
theorem analyticOrderAt_dyadicReciprocalGamma_int_of_neg
    (m : ℤ) (hm : m < 0) :
    analyticOrderAt dyadicReciprocalGamma (m : ℂ) =
      padicValNat 2 m.natAbs + 1 := by
  have hm0 : m ≠ 0 := by omega
  have hG :
      AnalyticAt ℂ dyadicReciprocalGamma (m : ℂ) :=
    dyadicReciprocalGamma_differentiable.analyticAt (m : ℂ)
  have hGneg :
      AnalyticAt ℂ
        (fun z : ℂ ↦ dyadicReciprocalGamma (-z)) (m : ℂ) := by
    have hneg : AnalyticAt ℂ (fun z : ℂ ↦ -z) (m : ℂ) := by
      fun_prop
    change AnalyticAt ℂ
      (dyadicReciprocalGamma ∘ fun z : ℂ ↦ -z) (m : ℂ)
    exact (dyadicReciprocalGamma_differentiable.analyticAt
      (-(m : ℂ))).comp hneg
  have hpos : dyadicReciprocalGamma (-(m : ℂ)) ≠ 0 := by
    simpa only [Int.cast_neg] using
      dyadicReciprocalGamma_int_ne_zero_of_nonneg (-m) (by omega)
  have hGnegOrder :
      analyticOrderAt
        (fun z : ℂ ↦ dyadicReciprocalGamma (-z)) (m : ℂ) = 0 :=
    hGneg.analyticOrderAt_eq_zero.mpr (by simpa using hpos)
  have href :
      dyadicReciprocalGamma *
          (fun z : ℂ ↦ dyadicReciprocalGamma (-z)) =
        rvachevFourierProduct := by
    funext z
    exact dyadicReciprocalGamma_mul_neg z
  calc
    analyticOrderAt dyadicReciprocalGamma (m : ℂ) =
        analyticOrderAt dyadicReciprocalGamma (m : ℂ) +
          analyticOrderAt
            (fun z : ℂ ↦ dyadicReciprocalGamma (-z)) (m : ℂ) := by
      rw [hGnegOrder, add_zero]
    _ = analyticOrderAt
          (dyadicReciprocalGamma *
            (fun z : ℂ ↦ dyadicReciprocalGamma (-z))) (m : ℂ) :=
      (analyticOrderAt_mul hG hGneg).symm
    _ = analyticOrderAt rvachevFourierProduct (m : ℂ) := by rw [href]
    _ = padicValNat 2 m.natAbs + 1 :=
      analyticOrderAt_rvachevFourierProduct_int m hm0

/-- Natural-number form of the exact zero order at `-n`. -/
theorem analyticOrderAt_dyadicReciprocalGamma_neg_nat
    (n : ℕ) (hn : n ≠ 0) :
    analyticOrderAt dyadicReciprocalGamma (-(n : ℂ)) =
      padicValNat 2 n + 1 := by
  have hneg : -(n : ℤ) < 0 := by omega
  simpa only [Int.ofNat_eq_natCast, Int.cast_neg, Int.cast_natCast,
    Int.natAbs_neg, Int.natAbs_natCast] using
    analyticOrderAt_dyadicReciprocalGamma_int_of_neg
      (-(n : ℤ)) hneg

/-- Mathlib records the pole of the dyadic Gamma function at a negative
integer as the negative of its order. -/
theorem meromorphicOrderAt_dyadicGamma_int_of_neg
    (m : ℤ) (hm : m < 0) :
    meromorphicOrderAt dyadicGamma (m : ℂ) =
      -((padicValNat 2 m.natAbs + 1 : ℕ) : WithTop ℤ) := by
  have hG :
      AnalyticAt ℂ dyadicReciprocalGamma (m : ℂ) :=
    dyadicReciprocalGamma_differentiable.analyticAt (m : ℂ)
  change meromorphicOrderAt (dyadicReciprocalGamma⁻¹) (m : ℂ) = _
  rw [meromorphicOrderAt_inv, hG.meromorphicOrderAt_eq,
    analyticOrderAt_dyadicReciprocalGamma_int_of_neg m hm,
    ← ENat.coe_one, ← ENat.coe_add, ENat.map_coe]
  norm_cast

/-- Natural-number form of the exact dyadic Gamma pole order at `-n`. -/
theorem meromorphicOrderAt_dyadicGamma_neg_nat
    (n : ℕ) (hn : n ≠ 0) :
    meromorphicOrderAt dyadicGamma (-(n : ℂ)) =
      -((padicValNat 2 n + 1 : ℕ) : WithTop ℤ) := by
  have hneg : -(n : ℤ) < 0 := by omega
  simpa only [Int.ofNat_eq_natCast, Int.cast_neg, Int.cast_natCast,
    Int.natAbs_neg, Int.natAbs_natCast] using
    meromorphicOrderAt_dyadicGamma_int_of_neg (-(n : ℤ)) hneg

end

end Fabius
