import OAI.Combinatorics.Progressions.Polynomial.PolynomialShearParameterBudget

namespace OAI

section

namespace Erdos3

theorem absolute_normalization_budget (C : ℕ) {p alpha : ℝ} (hp : 2 ≤ p)
    (halpha : 0 < alpha) (hlower : Real.exp (-p) ≤ alpha) :
    (p + 2) ^ C ≤ (p + 2) ^ (C + 1) ∧
      Real.exp (-((p + 2) ^ (C + 1))) / alpha ≤ Real.exp (-((p + 2) ^ C)) := by
  have hb : 1 ≤ p + 2 := by linarith
  have hpow : 1 ≤ (p + 2) ^ C := one_le_pow₀ hb
  have hs : (p + 2) ^ C + p ≤ (p + 2) ^ (C + 1) := by
    rw [pow_succ]
    nlinarith [mul_nonneg (by linarith : 0 ≤ p + 1) (sub_nonneg.mpr hpow)]
  refine ⟨by linarith, (div_le_iff₀ halpha).mpr ?_⟩
  calc
    _ ≤ Real.exp (-((p + 2) ^ C) - p) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-((p + 2) ^ C)) * Real.exp (-p) := by rw [sub_eq_add_neg, Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_left hlower (Real.exp_pos _).le

theorem exists_absolute_side_budget (Csc k : ℕ) (hk : 0 < k) {xi : ℝ} (hxi : 0 < xi) :
    ∃ C : ℕ, 2 ≤ C ∧ Csc < C ∧ ∀ p : ℝ, 2 ≤ p →
      (p + 2) ^ Csc ≤ (p + 2) ^ C ∧
      (64 * (k : ℝ)) ≤ Real.exp ((p + 2) ^ C) ∧
      100 * (1 + xi) * Real.exp ((p + 2) ^ Csc) ≤ Real.exp ((p + 2) ^ C) := by
  obtain ⟨ell, hell⟩ := exists_nat_ge (Real.log (64 * (k : ℝ)))
  obtain ⟨b, hb⟩ := exists_nat_ge (Real.log (100 * (1 + xi)))
  obtain ⟨D, hD, hbound⟩ := exists_natPolynomial_fixed_power_budget
    ((Polynomial.X + 2) ^ Csc + Polynomial.C ell + Polynomial.C b)
  let C := max D (Csc + 1)
  refine ⟨C, hD.trans (le_max_left _ _), by dsimp [C]; omega, ?_⟩
  intro p hp
  have hp0 : 0 ≤ p := by linarith
  have hbase : 1 ≤ p + 2 := by linarith
  have hpoly : (p + 2) ^ Csc + ell + b ≤ (p + 2) ^ D := by
    simpa [Polynomial.eval₂_pow] using hbound p hp0
  have hDC : (p + 2) ^ D ≤ (p + 2) ^ C := pow_le_pow_right₀ hbase (le_max_left _ _)
  have hsum := hpoly.trans hDC
  have hell0 : (0 : ℝ) ≤ ell := Nat.cast_nonneg _
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hpow0 : 0 ≤ (p + 2) ^ Csc := pow_nonneg (by linarith) _
  have hside : Real.log (64 * (k : ℝ)) ≤ (p + 2) ^ C := by linarith
  have hscore : Real.log (100 * (1 + xi)) + (p + 2) ^ Csc ≤ (p + 2) ^ C := by linarith
  refine ⟨by linarith, ?_, ?_⟩
  · calc
      _ = Real.exp (Real.log (64 * (k : ℝ))) := (Real.exp_log (by positivity)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hside
  · calc
      _ = Real.exp (Real.log (100 * (1 + xi)) + (p + 2) ^ Csc) := by
        rw [Real.exp_add, Real.exp_log (by positivity)]
      _ ≤ _ := Real.exp_le_exp.mpr hscore

end Erdos3

end

end OAI
