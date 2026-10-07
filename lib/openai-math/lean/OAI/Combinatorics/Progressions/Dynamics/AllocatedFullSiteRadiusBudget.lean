import OAI.Combinatorics.Progressions.Estimates.AllocatedFullSiteRadius
import OAI.Combinatorics.Progressions.Linear.BufferedCoordinateProjection

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (α : Type*) [Fintype α]

theorem allocatedFullSiteRadius_le_exp {P : ℝ} (hP : 0 ≤ P)
    (hm : (m : ℝ) ≤ Real.exp P) (hq : (Fintype.card α : ℝ) ≤ P)
    (hH : allocatedSiteRootAllowance α m ≤ Real.exp P)
    (hN : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp P) :
    (allocatedFullSiteRadius (G := G) B α : ℝ) ≤ Real.exp (4 * P + 1) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp : (2 : ℝ) ^ Fintype.card α ≤ Real.exp P := by
    calc
      _ ≤ (Real.exp 1) ^ Fintype.card α := pow_le_pow_left₀ (by norm_num) htwo _
      _ = Real.exp (Fintype.card α : ℝ) := by rw [← Real.exp_nat_mul]; simp only [mul_one]
      _ ≤ _ := Real.exp_le_exp.mpr hq
  have hj (j : Fin m) : allocatedSiteJetSize (G := G) B α j ≤ Real.exp (2 * P) := by
    calc
      _ ≤ _ := allocatedSiteJetSize_le_allowance B α j
      _ ≤ Real.exp P * Real.exp P := mul_le_mul (hN j) hH
        (zero_le_one.trans (allocatedSiteRootAllowance_one_le α m)) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hs : (∑ j : Fin m, allocatedSiteJetSize (G := G) B α j) ≤ Real.exp (3 * P) := by
    calc
      _ ≤ ∑ _j : Fin m, Real.exp (2 * P) := Finset.sum_le_sum (fun j _ => hj j)
      _ = (m : ℝ) * Real.exp (2 * P) := by simp
      _ ≤ Real.exp P * Real.exp (2 * P) := mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hmultip : (2 : ℝ) ^ Fintype.card α * ∑ j : Fin m, allocatedSiteJetSize (G := G) B α j ≤
      Real.exp (4 * P) := by
    calc
      _ ≤ Real.exp P * Real.exp (3 * P) := mul_le_mul hp hs
        (Finset.sum_nonneg (fun j _ => allocatedSiteJetSize_nonneg B α j)) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hunit : 1 ≤ Real.exp (4 * P) := Real.one_le_exp_iff.mpr (by positivity)
  change 1 + _ ≤ _
  calc
    _ ≤ Real.exp (4 * P) + Real.exp (4 * P) := add_le_add hunit hmultip
    _ = 2 * Real.exp (4 * P) := by ring
    _ ≤ Real.exp 1 * Real.exp (4 * P) := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem allocatedFullSiteRadius_buffered_lipschitz
    (p : LayerSamplerAxis I n → Prop) [DecidablePred p]
    (f : (LayerSamplerAxis I n → ℝ) → ℂ) {L : ℝ≥0}
    (hf : LipschitzWith L f) (hf1 : ∀ z, ‖f z‖ ≤ 1) :
    LipschitzWith (L + Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound)
      (bufferedCoordinateProjection p (allocatedFullSiteRadius (G := G) B α)
        (allocatedFullSiteRadius_pos B α) f) := by
  apply (bufferedCoordinateProjection_lipschitz p _ (allocatedFullSiteRadius_pos B α) f hf hf1).weaken
  apply add_le_add le_rfl
  have hden : (1 : ℝ≥0) ≤ 2 * allocatedFullSiteRadius (G := G) B α := by
    nlinarith [allocatedFullSiteRadius_one_le (G := G) B α]
  apply (div_le_iff₀ (zero_lt_one.trans_le hden)).mpr
  exact le_mul_of_one_le_right (by positivity) hden

end Erdos3.VectorPolynomial

end

end OAI
