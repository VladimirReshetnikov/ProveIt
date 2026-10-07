import OAI.Combinatorics.Progressions.Estimates.AllocatedTrimmedVectorSite

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)

theorem allocatedKernelNormalizedSlope_nonneg :
    0 ≤ (S.value : ℝ) / (1 + budget) :=
  div_nonneg (Nat.cast_nonneg _) (by
    have h := allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)
    linarith)

theorem allocatedKernelSlowBudget_le_one :
    (Fintype.card G : ℝ) * (S.value : ℝ) / (1 + budget) ≤ 1 := by
  have hcard : Fintype.card G ≤ Fintype.card (LayerSamplerVariables G I n B) :=
    Fintype.card_le_of_injective (Sum.inl : G → LayerSamplerVariables G I n B) Sum.inl_injective
  have hc : (Fintype.card G : ℝ) ≤ Fintype.card (LayerSamplerVariables G I n B) :=
    Nat.cast_le.mpr hcard
  have hden : 0 < 1 + budget := by
    have h := allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)
    linarith
  apply (div_le_one hden).mpr
  rw [allocatedPhysicalRootBudget_zero]
  exact (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)).trans (le_add_of_nonneg_left zero_le_one)

theorem allocatedKernelSlowBudget_abs_le_one :
    (Fintype.card G : ℝ) * |(S.value : ℝ) / (1 + budget)| ≤ 1 := by
  rw [abs_of_nonneg (allocatedKernelNormalizedSlope_nonneg B U basis S), ← mul_div_assoc]
  exact allocatedKernelSlowBudget_le_one B U basis S

theorem allocatedKernelSlowBudget_abs_bounds :
    0 ≤ (Fintype.card G : ℝ) * |(S.value : ℝ) / (1 + budget)| ∧
      (Fintype.card G : ℝ) * |(S.value : ℝ) / (1 + budget)| ≤ 1 :=
  ⟨mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _), allocatedKernelSlowBudget_abs_le_one B U basis S⟩

theorem allocatedKernelSlowBudget_toNNReal_le_one :
    Real.toNNReal ((Fintype.card G : ℝ) * |(S.value : ℝ) / (1 + budget)|) ≤ 1 := by
  exact Real.toNNReal_le_one.mpr
    (allocatedKernelSlowBudget_abs_le_one B U basis S)

end Erdos3.VectorPolynomial

end

end OAI
