import OAI.Combinatorics.Progressions.Estimates.JointComparisonTolerance

namespace OAI

section

namespace Erdos3

noncomputable def mixedCoefficientAccuracy (S τ : ℝ) : ℝ := τ/(2*(1+S))

theorem mixedCoefficientAccuracy_pos {S τ : ℝ} (hS : 0 ≤ S) (hτ : 0 < τ) :
    0 < mixedCoefficientAccuracy S τ := by unfold mixedCoefficientAccuracy; positivity

theorem mixedCoefficientAccuracy_le {S τ : ℝ} (hS : 0 ≤ S) (hτ : 0 ≤ τ) :
    mixedCoefficientAccuracy S τ ≤ τ := by
  exact div_le_self hτ (by linarith : 1 ≤ 2*(1+S))

theorem mixedComparisonError_le {S τ δ E : ℝ} (hS : 0 ≤ S) (hτ : 0 ≤ τ)
    (hδ : δ ≤ τ/2) (hE : E ≤ mixedCoefficientAccuracy S τ) : δ+E*S ≤ τ := by
  have hden : 0 < 2*(1+S) := by positivity
  have hmul : mixedCoefficientAccuracy S τ*S ≤ τ/2 := by
    unfold mixedCoefficientAccuracy
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hh := mul_le_mul_of_nonneg_right hE hS
  linarith

theorem mixedJointComparisonError_le (n : ℕ) {C G S τ δ ε η : ℝ}
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hS : 0 ≤ S) (hε : 0 ≤ ε)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hδ : δ ≤ τ/2)
    (he : ε ≤ vectorSpatialAccuracy n (2+G*C) (mixedCoefficientAccuracy S τ))
    (hη : η ≤ jointQuadratureAccuracy n G (mixedCoefficientAccuracy S τ)) :
    δ+(n*ε*(1+G*C+ε)^n+G^n*η)*S ≤ τ := by
  apply mixedComparisonError_le hS hτ.le hδ
  exact jointComparisonError_le n hC hG hε (mixedCoefficientAccuracy_pos hS hτ)
    ((mixedCoefficientAccuracy_le hS hτ.le).trans hτ1) he hη

theorem mixedCoefficientAccuracy_inverse_le_exp {S τ P : ℝ}
    (_hS : 0 ≤ S) (hτ : 0 < τ) (hP : 0 ≤ P)
    (hSP : S ≤ Real.exp P) (hτP : τ⁻¹ ≤ Real.exp P) :
    (mixedCoefficientAccuracy S τ)⁻¹ ≤ Real.exp (2*P+4) := by
  have hone : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  calc
    _ = 2*(1+S)*τ⁻¹ := by simp only [mixedCoefficientAccuracy, inv_div]; ring
    _ ≤ (4*Real.exp P)*Real.exp P :=
      mul_le_mul (by linarith) hτP (inv_nonneg.mpr hτ.le) (by positivity)
    _ = 4*Real.exp (2*P) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ Real.exp 4*Real.exp (2*P) := mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
