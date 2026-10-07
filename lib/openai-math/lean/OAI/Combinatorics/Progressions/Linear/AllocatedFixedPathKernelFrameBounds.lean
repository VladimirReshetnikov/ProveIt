import OAI.Combinatorics.Progressions.Probability.AllocatedFixedPathSlicedPhysicalDensityComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel
open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)
local notation "FullInput" => PrincipalTupleIndex B (layerSamplerDegree I n)

theorem allocatedFixedPathKernel_card_mul_scale_le_budget :
    (Fintype.card G : ℝ) * (S.value : ℝ) ≤ budget := by
  rw [allocatedPhysicalRootBudget_zero]
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Nat.cast_le.mpr (Fintype.card_le_of_injective
    (Sum.inl : G → LayerSamplerVariables G I n B) Sum.inl_injective)

theorem allocatedFixedPathKernelFrame_abs_le_one
    {τ ξ : ℝ} (hτ : 0 < τ) (hξ : 0 < ξ)
    (box : X → ℕ) (hbox : ∀ x, 0 < box x)
    (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hframe : integerFrame ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (G := G) (J := FullInput) budget τ ξ box) 1)
    (a : Option G × X) :
    |allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame a| ≤ 1 := by
  have hnorm := rectangularWeightIndices_normalized_norm_le _
    (narrowTrimmedSpatialWidths_pos
      (allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)) hτ hξ box hbox) hframe
  change |(integerFrame (canonicalZeroSpatialKernelEmbedding G FullInput X a) : ℝ) /
    narrowTrimmedSpatialWidths (G := G) (J := FullInput) budget τ ξ box
      (canonicalZeroSpatialKernelEmbedding G FullInput X a)| ≤ 1
  exact (Real.norm_eq_abs _).symm ▸
    (norm_le_pi_norm _ (canonicalZeroSpatialKernelEmbedding G FullInput X a)).trans hnorm

theorem allocatedFixedPathKernelFrame_geometry
    {τ ξ : ℝ} (hτ : 0 < τ) (hξ : 0 < ξ)
    (box : X → ℕ) (hbox : ∀ x, 0 < box x)
    (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hframe : integerFrame ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (G := G) (J := FullInput) budget τ ξ box) 1) :
    0 ≤ budget ∧ 0 ≤ (S.value : ℝ) ∧
      (Fintype.card G : ℝ) * (S.value : ℝ) ≤ budget ∧
      ∀ a, |allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame a| ≤ 1 :=
  ⟨allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0), Nat.cast_nonneg _,
    allocatedFixedPathKernel_card_mul_scale_le_budget B U basis S,
    allocatedFixedPathKernelFrame_abs_le_one B U basis S hτ hξ box hbox integerFrame hframe⟩

end Erdos3.VectorPolynomial

end

end OAI
