import OAI.Combinatorics.Progressions.Estimates.BufferedSiteExpansion

namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {D : Type*} [Fintype D]

noncomputable def smallBoxCutoff (x : D → ℝ) : ℝ :=
  max 0 (min 1 (3 - 8 * ‖x‖))

theorem smallBoxCutoff_range (x : D → ℝ) :
    0 ≤ smallBoxCutoff x ∧ smallBoxCutoff x ≤ 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem smallBoxCutoff_one (x : D → ℝ) (hx : ∀ i, |x i| ≤ 1/4) :
    smallBoxCutoff x = 1 := by
  have hn : ‖x‖ ≤ 1/4 := (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    (by simpa only [Real.norm_eq_abs] using hx)
  rw [smallBoxCutoff, min_eq_left (by linarith), max_eq_right (by norm_num)]

theorem smallBoxCutoff_zero (x : D → ℝ) (hx : 3/8 ≤ ‖x‖) :
    smallBoxCutoff x = 0 := by
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

theorem smallBoxCutoff_support (x : D → ℝ) (hx : smallBoxCutoff x ≠ 0) :
    ∀ i, |x i| < 1/2 := by
  have hn : ‖x‖ < 3/8 := lt_of_not_ge (fun h => hx (smallBoxCutoff_zero x h))
  intro i
  have hi : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
  linarith

theorem smallBoxCutoff_lipschitz : LipschitzWith 8 (smallBoxCutoff (D := D)) := by
  have h : LipschitzWith 8 (fun x : D → ℝ => 3 - 8 * ‖x‖) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq]
    have he : (3 - 8 * ‖x‖) - (3 - 8 * ‖y‖) = -8 * (‖x‖ - ‖y‖) := by ring
    rw [he, abs_mul]
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8), NNReal.coe_ofNat]
    exact mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using abs_norm_sub_norm_le x y)
      (by norm_num)
  exact (h.const_min 1).const_max 0

theorem smallBoxCutoff_mul_lipschitz (f : (D → ℝ) → ℝ) {L B : ℝ≥0}
    (hf : LipschitzWith L f) (hb : ∀ x, |f x| ≤ B) :
    LipschitzWith (L + B * 8) (fun x => smallBoxCutoff x * f x) := by
  simpa only [one_mul] using lipschitz_real_mul_of_bounds (Bf := 1) (Bg := B) smallBoxCutoff f
    smallBoxCutoff_lipschitz hf
    (fun x => by rw [abs_of_nonneg (smallBoxCutoff_range x).1]; exact (smallBoxCutoff_range x).2) hb

end Erdos3

end

end OAI
