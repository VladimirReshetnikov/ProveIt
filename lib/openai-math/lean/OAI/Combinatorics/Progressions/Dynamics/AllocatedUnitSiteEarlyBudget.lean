import OAI.Combinatorics.Progressions.Geometry.AllocatedSupportedBufferedPhysicalFactorization

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (α : Type*) [Fintype α]

theorem allocatedBufferedPhysicalChartRadius_le_one
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (j : Fin m) :
    allocatedBufferedPhysicalChartRadius (G := G) B α C j ≤ 1 := by
  have hCj := hC j
  have hr := allocatedFullSiteRadius_one_le (G := G) B α
  have hden : 1 ≤ 8 * (C j + 1) * ((Fintype.card (I j) : ℝ) + 1) *
      (allocatedFullSiteRadius (G := G) B α : ℝ) := by
    calc
      (1 : ℝ) ≤ 8 * 1 * 1 * 1 := by norm_num
      _ ≤ _ := by
        gcongr
        · linarith
        · exact le_add_of_nonneg_left (Nat.cast_nonneg _)
        · exact_mod_cast hr
  unfold allocatedBufferedPhysicalChartRadius
  apply (min_le_right _ _).trans
  exact (div_le_one (lt_of_lt_of_le zero_lt_one hden)).2 hden

theorem allocatedBufferedPhysicalChartRadius_inv_le_exp_uniform
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) {P : ℝ} (hP : 0 ≤ P)
    (hm : (m : ℝ) ≤ Real.exp P) (hq : (Fintype.card α : ℝ) ≤ P)
    (hallow : ((2 * m : ℕ) + 5) * (Fintype.card α : ℝ) + 5 ≤ P)
    (hCP : ∀ j, C j ≤ Real.exp P)
    (hNP : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp P)
    (hIP : ∀ j, (Fintype.card (I j) : ℝ) ≤ Real.exp P) (j : Fin m) :
    (allocatedBufferedPhysicalChartRadius (G := G) B α C j)⁻¹ ≤
      Real.exp (((m : ℝ) + 10) * (P + Fintype.card α + 2)) := by
  apply (allocatedBufferedPhysicalChartRadius_inv_le_exp B α C hC hP hm hq hallow hCP hNP hIP j).trans
  apply Real.exp_le_exp.mpr
  have hj : ((j.val + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt j.isLt
  have hfactor : 0 ≤ P + (Fintype.card α : ℝ) + 1 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hj hfactor
  have hq0 : (0 : ℝ) ≤ Fintype.card α := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  nlinarith

end Erdos3.VectorPolynomial

end

end OAI
