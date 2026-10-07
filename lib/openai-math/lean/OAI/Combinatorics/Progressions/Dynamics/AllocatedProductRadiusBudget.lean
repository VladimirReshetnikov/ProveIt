import OAI.Combinatorics.Progressions.Estimates.AllocatedProductIdealCutoff

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

noncomputable def allocatedProductGridRadius (C : Fin m → ℝ) (j : Fin m) : ℝ :=
  finiteRowChartRadius (((rowSets j).card + 1) * Fintype.card (Finset α))
    (Fintype.card (I j)) (C j) (2 * (allocatedProductIdealSiteRadius (G := G) B rowSets : ℝ))

theorem allocatedProductGridRadius_pos (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (j : Fin m) :
    0 < allocatedProductGridRadius (G := G) B rowSets C j :=
  finiteRowChartRadius_pos _ _ (hC j)
    (mul_nonneg (by norm_num) (allocatedProductIdealSiteRadius (G := G) B rowSets).coe_nonneg)

theorem allocatedProductGridRadius_recovery_budget
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) {R : Fin m → ℝ} (hR : ∀ j, 0 ≤ R j)
    (hsmall : ∀ j, R j ≤ allocatedProductGridRadius (G := G) B rowSets C j) (j : Fin m) :
    ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) *
        (2 * (allocatedProductIdealSiteRadius (G := G) B rowSets : ℝ) * R j)))) ≤ 1 / 4 := by
  have h := finiteRowChartRadius_budget (((rowSets j).card + 1) * Fintype.card (Finset α))
    (Fintype.card (I j)) (hC j)
    (mul_nonneg (by norm_num) (allocatedProductIdealSiteRadius (G := G) B rowSets).coe_nonneg)
    (hR j) (hsmall j)
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_assoc] using h

theorem allocatedProductGridRadius_source_budget
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) {R : Fin m → ℝ} (hR : ∀ j, 0 ≤ R j)
    (hsmall : ∀ j, R j ≤ allocatedProductGridRadius (G := G) B rowSets C j) (j : Fin m) :
    C j * (((Fintype.card (I j) : ℝ) + 1) *
      (2 * (allocatedProductIdealSiteRadius (G := G) B rowSets : ℝ) * R j)) ≤ 1 / 4 := by
  have hcard : (1 : ℝ) ≤ Fintype.card (Finset α) := by
    exact_mod_cast Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr ⟨(∅ : Finset α)⟩)
  have hrow : (0 : ℝ) ≤ (rowSets j).card := Nat.cast_nonneg _
  have hfactor : (1 : ℝ) ≤ ((rowSets j).card + 1 : ℝ) * Fintype.card (Finset α) := by nlinarith
  have hc : 0 ≤ C j * (((Fintype.card (I j) : ℝ) + 1) *
      (2 * (allocatedProductIdealSiteRadius (G := G) B rowSets : ℝ) * R j)) :=
    mul_nonneg (hC j) (mul_nonneg (by positivity)
      (mul_nonneg (mul_nonneg (by norm_num) (allocatedProductIdealSiteRadius (G := G) B rowSets).coe_nonneg) (hR j)))
  have h := mul_le_mul_of_nonneg_right hfactor hc
  have hb := allocatedProductGridRadius_recovery_budget B rowSets C hC hR hsmall j
  simp only [one_mul, mul_assoc] at h hb ⊢
  exact h.trans hb

end Erdos3.VectorPolynomial

end

end OAI
