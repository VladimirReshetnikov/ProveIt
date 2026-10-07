import OAI.Combinatorics.Progressions.Estimates.RealifiedReconstruction

namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem exists_rationalReconstructionLipschitzBound_exp (s : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ (d n H : ℕ) (ℓ B : ℝ≥0) (p : ℝ),
      0 ≤ p → (d : ℝ) ≤ p → (n : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (ℓ : ℝ) ≤ Real.exp p → (B : ℝ) ≤ Real.exp p →
      (rationalReconstructionLipschitzBound s d n H ℓ B : ℝ) ≤ Real.exp ((p + N) ^ N) := by
  obtain ⟨D, hD, hbox⟩ := exists_bchBoxMetricConstant_exp_bound s 0
  let N := D + 20
  refine ⟨N, by dsimp [N]; omega, ?_⟩
  intro d n H ℓ B p hp hd hn hH hℓ hB
  let t := p + N
  let q := t ^ (N - 1)
  have ht : 5 ≤ t := by
    have : (20 : ℝ) ≤ N := by exact_mod_cast (show 20 ≤ N by dsimp [N]; omega)
    dsimp [t]
    linarith
  have hq1 : 1 ≤ q := one_le_pow₀ (by linarith : (1 : ℝ) ≤ t)
  have hpq : p ≤ q := by
    apply (show p ≤ t from le_add_of_nonneg_right (Nat.cast_nonneg N)).trans
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ t)
      (show 1 ≤ N - 1 by dsimp [N]; omega)
  have hpe : Real.exp p ≤ Real.exp q := Real.exp_le_exp.mpr hpq
  have htwo : (2 : ℝ) ≤ Real.exp q := by
    linarith [Real.add_one_le_exp q]
  let C := bchLogMetricConstant s n H 1
  have hC : (C : ℝ) ≤ Real.exp q := by
    have hbc := (bchBoxCoordinateBound_le_bchBoxMetricConstant s n H 1).trans
      (hbox n H 1 p hp hn hH (by simp only [NNReal.coe_one, pow_zero]; exact Real.one_le_exp (by norm_num)))
    change bchBoxCoordinateBound s n H 1 ≤ Real.exp ((p + D) ^ D) at hbc
    have hqt : (p + D) ^ D + 1 ≤ q := by
      calc
        (p + D) ^ D + 1 ≤ t ^ D + t ^ D := by
          gcongr
          · dsimp [t, N]; push_cast; linarith
          · exact one_le_pow₀ (by linarith : (1 : ℝ) ≤ t)
        _ ≤ t * t ^ D := by nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ t) D]
        _ = t ^ (D + 1) := (pow_succ' t D).symm
        _ ≤ q := pow_le_pow_right₀ (by linarith) (by dsimp [N]; omega)
    change bchBoxCoordinateBound s n H 1 + 1 ≤ Real.exp q
    calc
      _ ≤ Real.exp ((p + D) ^ D) + Real.exp ((p + D) ^ D) := by
        linarith [Real.one_le_exp (by positivity : 0 ≤ (p + D) ^ D)]
      _ ≤ Real.exp ((p + D) ^ D) * Real.exp 1 := by
        have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        nlinarith [Real.exp_pos ((p + D) ^ D)]
      _ = Real.exp ((p + D) ^ D + 1) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hqt
  let A := coordinateLipschitzBound d n (rationalSolveHeight n H)
  have hA : (A : ℝ) ≤ Real.exp q := by
    have hpp : p ≤ (p + 2) ^ 5 := le_power_budget hp (by decide)
    have hA' := coordinateLipschitzBound_le_exp d n (rationalSolveHeight n H)
      (by positivity : 0 ≤ (p + 2) ^ 5) (hd.trans hpp) (hn.trans hpp)
      (by exact_mod_cast rationalSolveHeight_le_budget n H hp hn hH)
    apply hA'.trans
    apply Real.exp_le_exp.mpr
    apply (shifted_power_budget_le hp 5 2).trans
    change (p + 2) ^ 14 ≤ q
    calc
      _ ≤ t ^ 14 := pow_le_pow_left₀ (by linarith) (by dsimp [t, N]; push_cast; linarith) 14
      _ ≤ q := pow_le_pow_right₀ (by linarith) (by dsimp [N]; omega)
  have hdim : (n : ℝ) + 1 ≤ Real.exp q :=
    (show (n : ℝ) + 1 ≤ p + 1 by linarith).trans ((Real.add_one_le_exp p).trans hpe)
  have hfirst : (ℓ : ℝ) * (2 * ((A : ℝ) * ((n : ℝ) + 1) * C)) ≤ Real.exp (5 * q) := by
    calc
      _ ≤ Real.exp q * (Real.exp q * (Real.exp q * Real.exp q * Real.exp q)) := by
        gcongr
        · exact hℓ.trans hpe
      _ = Real.exp (5 * q) := by simp only [← Real.exp_add]; congr 1; ring
  have hsecond : 2 * (B : ℝ) / ((C : ℝ)⁻¹ / 2) ≤ Real.exp (5 * q) := by
    calc
      _ = 2 * 2 * (B : ℝ) * C := by simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]; ring
      _ ≤ Real.exp q * Real.exp q * Real.exp q * Real.exp q := by gcongr; exact hB.trans hpe
      _ = Real.exp (4 * q) := by simp only [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (5 * q) := Real.exp_le_exp.mpr (by linarith)
  have hmax : (rationalReconstructionLipschitzBound s d n H ℓ B : ℝ) ≤ Real.exp (5 * q) := by
    change max ((ℓ : ℝ) * (2 * ((A : ℝ) * ((n : ℝ) + 1) * C)))
      (2 * (B : ℝ) / ((C : ℝ)⁻¹ / 2)) ≤ _
    exact max_le hfirst hsecond
  apply hmax.trans
  apply Real.exp_le_exp.mpr
  calc
    5 * q ≤ t * q := mul_le_mul_of_nonneg_right ht (by dsimp [q]; positivity)
    _ = (p + N) ^ N := by dsimp [q, t]; rw [← pow_succ', Nat.sub_add_cancel (by dsimp [N]; omega)]

end Erdos3

end

end OAI
