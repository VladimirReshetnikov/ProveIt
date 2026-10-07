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
  have ht0 : (0 : Real) < t := by exact_mod_cast (show 0 < t by omega)
  have hq0 : (0 : Real) < q := by exact_mod_cast hq
  have hqtR : (q : Real) ≤ t := by exact_mod_cast hqt
  have happrox' : |alpha - (a : Real) / (q : Real)| ≤ ((q : Real) ^ 2)⁻¹ := by
    apply happrox.trans
    apply inv_anti₀ (by positivity)
    nlinarith
  have hcop : Int.gcd a (q : Int) = 1 := by simpa only [Int.gcd, Int.natAbs_natCast] using haq
  have h := weyl_raised_estimate (alpha := alpha) (k := 2) (m := 2)
    (by omega) ht ht (by omega) a (q : Int) (by exact_mod_cast hq) hcop
    (by simpa only [Int.cast_natCast] using happrox')
  have hcoef : weylRaisedCoefficientAt 2 2 ≤ (2 : Real) ^ (25 : Nat) := by
    norm_num [weylRaisedCoefficientAt, weylDifferencingPower]
  have hrat : weylRationalFactor 2 t (q : Int) ≤ (q : Real)⁻¹ + 2 / t := by
    have hterm : (q : Real) / (t : Real) ^ 2 ≤ 1 / t := by
      apply (div_le_div_iff₀ (by positivity) ht0).mpr
      nlinarith
    simp only [weylRationalFactor, Int.cast_natCast, Nat.cast_ofNat,
      Real.rpow_neg ht0.le, Real.rpow_two]
    change (q : Real)⁻¹ + (t : Real)⁻¹ + (q : Real) * ((t : Real) ^ 2)⁻¹ ≤ _
    have heq : (t : Real)⁻¹ + 1 / t = 2 / t := by ring
    rw [← heq]
    simpa only [div_eq_mul_inv, add_assoc, add_comm, add_left_comm] using
      add_le_add_left hterm ((q : Real)⁻¹ + (t : Real)⁻¹)
  have hlog : 0 ≤ 1 + Real.log (t : Real) := by
    have ht1 : (1 : Real) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
    linarith [Real.log_nonneg ht1]
  have hpow : (t : Real) ^ ((2 : Real) + 1 / 2) = (t : Real) ^ 2 * Real.sqrt t := by
    rw [Real.rpow_add ht0, Real.rpow_two, Real.sqrt_eq_rpow]
  have hbase : ‖weylSum alpha 2 t‖ ^ 2 ≤
      weylRaisedCoefficientAt 2 2 * ((t : Real) ^ 2 * Real.sqrt t) *
        weylRationalFactor 2 t (q : Int) * (1 + Real.log t) := by
    simpa only [weylDifferencingPower, Nat.reduceSub, Nat.reducePow, Nat.cast_ofNat, Nat.cast_one,
      one_pow, one_div, ← hpow] using h
  have hrat0 : 0 ≤ weylRationalFactor 2 t (q : Int) := by
    unfold weylRationalFactor
    positivity
  have hupper : ‖weylSum alpha 2 t‖ ^ 2 ≤
      (2 ^ (25 : Nat) * Real.sqrt t * ((q : Real)⁻¹ + 2 / t) * (1 + Real.log t)) *
        (t : Real) ^ 2 := by
    calc
      _ ≤ _ := hbase
      _ ≤ (2 : Real) ^ (25 : Nat) * ((t : Real) ^ 2 * Real.sqrt t) *
          ((q : Real)⁻¹ + 2 / t) * (1 + Real.log t) := by gcongr
      _ = _ := by ring
  exact (div_le_iff₀ (by positivity)).mpr hupper

end LeanProofs.GowersSzemeredi
