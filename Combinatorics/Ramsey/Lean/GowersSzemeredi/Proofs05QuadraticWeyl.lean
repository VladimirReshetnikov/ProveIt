import GowersSzemeredi.Proofs05Weyl
import GowersSzemeredi.Proofs05QuadraticRecurrenceBudget

/-! A finite normalized quadratic Weyl estimate. Specializing the checked
differencing argument at divisor parameter two avoids its later, much
larger, asymptotic threshold. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem quadratic_weyl_normalized {t q : Nat} (ht : 2 ≤ t) (hq : 0 < q)
    (hqt : q ≤ t) (a : Int) (alpha : Real) (haq : Nat.Coprime a.natAbs q)
    (happrox : |alpha - (a : Real) / q| ≤ ((q : Real) * t)⁻¹) :
    ‖weylSum alpha 2 t‖ ^ 2 / (t : Real) ^ 2 ≤
      2 ^ (25 : Nat) * Real.sqrt t * ((q : Real)⁻¹ + 2 / t) * (1 + Real.log t) := by
  have ht0 : (0 : Real) < t := by positivity
  have hqtR : (q : Real) ≤ t := by exact_mod_cast hqt
  have h := weyl_raised_estimate (alpha := alpha) (k := 2) (m := 2)
    (by omega) ht ht (by omega) a (q : Int) (by exact_mod_cast hq)
    (by simpa only [Int.gcd, Int.natAbs_natCast] using haq)
    (by simpa only [Int.cast_natCast] using
      happrox.trans (inv_anti₀ (by positivity) (by nlinarith : (q : Real) ^ 2 ≤ q * t)))
  have hcoef : weylRaisedCoefficientAt 2 2 ≤ (2 : Real) ^ (25 : Nat) := by
    norm_num [weylRaisedCoefficientAt, weylDifferencingPower]
  have hrat0 : 0 ≤ weylRationalFactor 2 t (q : Int) := by unfold weylRationalFactor; positivity
  -- `weylRationalFactor 2 t q = q⁻¹ + t⁻¹ + q / t ^ 2`, and `q / t ^ 2 ≤ t⁻¹`
  have hrat : weylRationalFactor 2 t (q : Int) ≤ (q : Real)⁻¹ + 2 / t := by
    have h1 : (q : Real) * (t : Real) ^ (-(2 : Real)) ≤ (t : Real)⁻¹ := by
      rw [Real.rpow_neg ht0.le, Real.rpow_two, ← div_eq_mul_inv, div_le_iff₀ (pow_pos ht0 2), sq,
        ← mul_assoc, inv_mul_cancel₀ ht0.ne', one_mul]
      exact hqtR
    simp only [weylRationalFactor, Int.cast_natCast, Nat.cast_ofNat]
    linarith [div_eq_mul_inv (2 : Real) t]
  rw [div_le_iff₀ (pow_pos ht0 2)]
  calc ‖weylSum alpha 2 t‖ ^ 2 ≤ weylRaisedCoefficientAt 2 2 * ((t : Real) ^ 2 * Real.sqrt t) *
        weylRationalFactor 2 t (q : Int) * (1 + Real.log t) := by
        simpa only [weylDifferencingPower, Nat.reduceSub, Nat.reducePow, Nat.cast_ofNat,
          Nat.cast_one, one_pow, Real.rpow_add ht0, Real.rpow_two, ← Real.sqrt_eq_rpow] using h
    _ ≤ 2 ^ (25 : Nat) * ((t : Real) ^ 2 * Real.sqrt t) * ((q : Real)⁻¹ + 2 / t) *
        (1 + Real.log t) := by gcongr
    _ = _ := by ring

end LeanProofs.GowersSzemeredi
