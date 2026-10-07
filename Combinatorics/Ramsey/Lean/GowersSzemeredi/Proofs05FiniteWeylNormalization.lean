import GowersSzemeredi.Proofs05Weyl

/-! Normalize the finite Weyl estimate before choosing the divisor parameter
or a recurrence scale. Dirichlet approximation at order `t^(k-1)` bounds
both rational-error terms by `1/t`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem weyl_normalized_finite {k t m q : Nat}
    (hk : 2 ≤ k) (ht : 2 ≤ t) (hkt : k ≤ t) (hm : 1 ≤ m) (hq : 0 < q)
    (hqt : q ≤ t ^ (k - 1)) (a : Int) (alpha : Real) (haq : Nat.Coprime a.natAbs q)
    (happrox : |alpha - (a : Real) / q| ≤ ((q : Real) * (t : Real) ^ (k - 1))⁻¹) :
    ‖weylSum alpha k t‖ ^ weylDifferencingPower k / (t : Real) ^ weylDifferencingPower k ≤
      weylRaisedCoefficientAt k m *
        (t : Real) ^ ((((k - 1 : Nat) : Real) ^ 2) / m) *
        ((q : Real)⁻¹ + 2 / t) * (1 + Real.log t) := by
  have ht0 : (0 : Real) < t := by exact_mod_cast (show 0 < t by omega)
  have hq0 : (0 : Real) < q := by exact_mod_cast hq
  have hqtR : (q : Real) ≤ (t : Real) ^ (k - 1) := by exact_mod_cast hqt
  have happrox' : |alpha - (a : Real) / q| ≤ ((q : Real) ^ 2)⁻¹ := by
    apply happrox.trans
    apply inv_anti₀ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hqtR hq0.le]
  have hcop : Int.gcd a (q : Int) = 1 := by simpa only [Int.gcd, Int.natAbs_natCast] using haq
  have h := weyl_raised_estimate hk ht hkt hm a (q : Int) (by exact_mod_cast hq) hcop
    (by simpa only [Int.cast_natCast] using happrox')
  have hpow : (t : Real) ^ (k - 1) * t = (t : Real) ^ k := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
  have hrat : weylRationalFactor k t (q : Int) ≤ (q : Real)⁻¹ + 2 / t := by
    have hterm : (q : Real) / (t : Real) ^ k ≤ 1 / t := by
      apply (div_le_div_iff₀ (by positivity) ht0).mpr
      rw [one_mul, ← hpow]
      exact mul_le_mul_of_nonneg_right hqtR ht0.le
    simp only [weylRationalFactor, Int.cast_natCast, Real.rpow_neg ht0.le, Real.rpow_natCast]
    have heq : (t : Real)⁻¹ + 1 / t = 2 / t := by ring
    rw [← heq]
    simpa only [div_eq_mul_inv, add_assoc, add_comm, add_left_comm] using
      add_le_add_left hterm ((q : Real)⁻¹ + (t : Real)⁻¹)
  have hlog : 0 ≤ 1 + Real.log (t : Real) := by
    have ht1 : (1 : Real) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
    linarith [Real.log_nonneg ht1]
  have hcoef : 0 ≤ weylRaisedCoefficientAt k m := by
    unfold weylRaisedCoefficientAt
    positivity
  have hbase := h
  rw [Real.rpow_add ht0, Real.rpow_natCast] at hbase
  apply (div_le_iff₀ (by positivity)).mpr
  calc
    _ ≤ _ := hbase
    _ ≤ weylRaisedCoefficientAt k m *
        ((t : Real) ^ weylDifferencingPower k * (t : Real) ^ ((((k - 1 : Nat) : Real) ^ 2) / m)) *
        ((q : Real)⁻¹ + 2 / t) * (1 + Real.log t) := by gcongr
    _ = _ := by ring

end LeanProofs.GowersSzemeredi
