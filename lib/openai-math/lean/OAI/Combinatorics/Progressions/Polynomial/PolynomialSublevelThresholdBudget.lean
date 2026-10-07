import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OAI


namespace Erdos3

noncomputable def polynomialSublevelThreshold (n m : ℕ) (C scale η : ℝ) : ℝ :=
  (2 * (1 + scale) * (1 + 2 * C * (m + 1 : ℝ) / η) ^ n)⁻¹

theorem polynomialSublevelThreshold_pos (n m : ℕ) {C scale η : ℝ}
    (hC : 0 ≤ C) (hs : 0 ≤ scale) (hη : 0 < η) :
    0 < polynomialSublevelThreshold n m C scale η := by
  unfold polynomialSublevelThreshold
  positivity

theorem polynomialSublevelThreshold_le_half (n m : ℕ) {C scale η : ℝ}
    (hC : 0 ≤ C) (hs : 0 ≤ scale) (hη : 0 < η) :
    polynomialSublevelThreshold n m C scale η ≤ 1 / 2 := by
  have hL : 1 ≤ 1 + 2 * C * (m + 1 : ℝ) / η := by
    have hbase : 0 ≤ 2 * C * (m + 1 : ℝ) / η := by positivity
    linarith
  have hpow : 1 ≤ (1 + 2 * C * (m + 1 : ℝ) / η) ^ n := one_le_pow₀ hL
  have hden : 2 ≤ 2 * (1 + scale) * (1 + 2 * C * (m + 1 : ℝ) / η) ^ n := by
    nlinarith
  simpa only [polynomialSublevelThreshold, one_div] using
    one_div_le_one_div_of_le (by norm_num) hden

theorem polynomialSublevelThreshold_root_bound {n m : ℕ} (hn : 0 < n)
    {C scale η : ℝ} (hC : 0 ≤ C) (hs : 0 ≤ scale) (hη : 0 < η) :
    (2 * polynomialSublevelThreshold n m C scale η * scale) ^ ((n : ℝ)⁻¹) ≤
      (1 + 2 * C * (m + 1 : ℝ) / η)⁻¹ := by
  let L := 1 + 2 * C * (m + 1 : ℝ) / η
  have hL : 0 < L := by dsimp [L]; positivity
  have hscale : 0 < 1 + scale := by linarith
  have he : 2 * polynomialSublevelThreshold n m C scale η * scale =
      (scale / (1 + scale)) * (L ^ n)⁻¹ := by
    unfold polynomialSublevelThreshold
    dsimp only [L]
    field_simp
  have hfrac : scale / (1 + scale) ≤ 1 := (div_le_one hscale).mpr (by linarith)
  have hsmall : 2 * polynomialSublevelThreshold n m C scale η * scale ≤ (L ^ n)⁻¹ := by
    rw [he]
    exact mul_le_of_le_one_left (by positivity) hfrac
  have hnonneg : 0 ≤ 2 * polynomialSublevelThreshold n m C scale η * scale :=
    mul_nonneg (mul_nonneg (by norm_num) (polynomialSublevelThreshold_pos n m hC hs hη).le) hs
  calc
    _ ≤ ((L ^ n)⁻¹) ^ ((n : ℝ)⁻¹) := Real.rpow_le_rpow hnonneg hsmall (by positivity)
    _ = L⁻¹ := by
      rw [Real.inv_rpow (pow_nonneg hL.le n), Real.pow_rpow_inv_natCast hL.le hn.ne']

theorem polynomialSublevelThreshold_total_bound {n m : ℕ} (hn : 0 < n)
    {C scale η : ℝ} (hC : 0 ≤ C) (hs : 0 ≤ scale) (hη : 0 < η) :
    (m : ℝ) * C * (2 * polynomialSublevelThreshold n m C scale η * scale) ^ ((n : ℝ)⁻¹) ≤
      η / 2 := by
  let L := 1 + 2 * C * (m + 1 : ℝ) / η
  have hL : 0 < L := by dsimp [L]; positivity
  have he : (η / 2) * L = η / 2 + C * (m + 1 : ℝ) := by
    dsimp only [L]
    field_simp
  calc
    _ ≤ (m : ℝ) * C * L⁻¹ := mul_le_mul_of_nonneg_left
      (polynomialSublevelThreshold_root_bound hn hC hs hη) (by positivity)
    _ ≤ η / 2 := by
      rw [← div_eq_mul_inv]
      apply (div_le_iff₀ hL).mpr
      rw [he]
      nlinarith

theorem polynomialSublevelThreshold_log_inv (n m : ℕ) {C scale η : ℝ}
    (hC : 0 ≤ C) (hs : 0 ≤ scale) (hη : 0 < η) :
    Real.log (polynomialSublevelThreshold n m C scale η)⁻¹ =
      Real.log 2 + Real.log (1 + scale) +
        (n : ℝ) * Real.log (1 + 2 * C * (m + 1 : ℝ) / η) := by
  have hscale : 0 < 1 + scale := by linarith
  have hL : 0 < 1 + 2 * C * (m + 1 : ℝ) / η := by positivity
  rw [polynomialSublevelThreshold, inv_inv,
    Real.log_mul (mul_pos (by norm_num) hscale).ne' (pow_pos hL n).ne',
    Real.log_mul (by norm_num) hscale.ne', Real.log_pow]


theorem polynomialSublevelThreshold_log_budget (n m : ℕ) {C scale η P : ℝ}
    (hC : 0 ≤ C) (hs : 0 ≤ scale) (hη : 0 < η) (hP : 0 ≤ P)
    (hCP : C ≤ Real.exp P) (hsP : scale ≤ Real.exp P)
    (hmP : (m + 1 : ℝ) ≤ Real.exp P) (hηP : η⁻¹ ≤ Real.exp P) :
    Real.log (polynomialSublevelThreshold n m C scale η)⁻¹ ≤
      (1 + 3 * (n : ℝ)) * P + 2 * Real.log 2 + (n : ℝ) * Real.log 3 := by
  have hE : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have hE3 : 1 ≤ Real.exp (3 * P) := Real.one_le_exp_iff.mpr (by positivity)
  have hscale : 1 + scale ≤ 2 * Real.exp P := by linarith
  have hprod : C * (m + 1 : ℝ) * η⁻¹ ≤ Real.exp P * Real.exp P * Real.exp P :=
    mul_le_mul (mul_le_mul hCP hmP (by positivity) (Real.exp_pos P).le) hηP
      (inv_nonneg.mpr hη.le) (by positivity)
  have heq : Real.exp P * Real.exp P * Real.exp P = Real.exp (3 * P) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [heq] at hprod
  have hquot : 2 * C * (m + 1 : ℝ) / η ≤ 2 * Real.exp (3 * P) := by
    have ht := mul_le_mul_of_nonneg_left hprod (show (0 : ℝ) ≤ 2 by norm_num)
    simpa only [div_eq_mul_inv, mul_assoc] using ht
  have hinner : 1 + 2 * C * (m + 1 : ℝ) / η ≤ 3 * Real.exp (3 * P) := by linarith
  have hlogs := Real.log_le_log (show 0 < 1 + scale by positivity) hscale
  rw [Real.log_mul (by norm_num) (Real.exp_ne_zero P), Real.log_exp] at hlogs
  have hlogL := Real.log_le_log (show 0 < 1 + 2 * C * (m + 1 : ℝ) / η by positivity) hinner
  rw [Real.log_mul (by norm_num) (Real.exp_ne_zero (3 * P)), Real.log_exp] at hlogL
  rw [polynomialSublevelThreshold_log_inv n m hC hs hη]
  calc
    _ ≤ Real.log 2 + (Real.log 2 + P) + (n : ℝ) * (Real.log 3 + 3 * P) :=
      add_le_add (add_le_add le_rfl hlogs) (mul_le_mul_of_nonneg_left hlogL (Nat.cast_nonneg n))
    _ = _ := by ring

end Erdos3

end OAI
