import Mathlib.MeasureTheory.Integral.Pi
import OAI.Combinatorics.Progressions.Probability.DensityMixtureAELaw

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {X : Type*}

def fixedSpatialEmptyIndex : (Σ _ : X, Unit ⊕ Empty) ≃ X where
  toFun a := a.1
  invFun x := ⟨x, .inl ()⟩
  left_inv a := by
    rcases a with ⟨x, u | e⟩
    · cases u
      rfl
    · exact isEmptyElim e
  right_inv _ := rfl

variable [Fintype X]

noncomputable def fixedSpatialEmptyCoordinates :
    (X → ℝ) ≃ₗᵢ[ℝ] ((Σ _ : X, Unit ⊕ Empty) → ℝ) where
  toFun u a := u a.1
  invFun v x := v ⟨x, .inl ()⟩
  left_inv _ := rfl
  right_inv v := by
    funext a
    rcases a with ⟨x, u | e⟩
    · cases u
      rfl
    · exact isEmptyElim e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' u := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr
      intro a
      exact norm_le_pi_norm u a.1
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (fun a : Σ _ : X, Unit ⊕ Empty => u a.1))).mpr
      intro x
      exact norm_le_pi_norm (fun a : Σ _ : X, Unit ⊕ Empty => u a.1) ⟨x, .inl ()⟩

theorem fixedSpatialEmptyCoordinates_apply (u : X → ℝ) (a : Σ _ : X, Unit ⊕ Empty) :
    fixedSpatialEmptyCoordinates u a = u a.1 := rfl

theorem fixedSpatialEmptyCoordinates_symm_apply
    (v : (Σ _ : X, Unit ⊕ Empty) → ℝ) (x : X) :
    fixedSpatialEmptyCoordinates.symm v x = v ⟨x, .inl ()⟩ := rfl

theorem fixedSpatialEmptyCoordinates_measurePreserving :
    MeasurePreserving (fixedSpatialEmptyCoordinates (X := X)) volume volume := by
  have hp := volume_measurePreserving_piCongrLeft (fun _ : Σ _ : X, Unit ⊕ Empty => ℝ)
    (fixedSpatialEmptyIndex (X := X)).symm
  convert hp using 1
  funext u a
  rcases a with ⟨x, v | e⟩
  · cases v
    rfl
  · exact isEmptyElim e

theorem fixedSpatialEmptyCoordinates_symm_measurePreserving :
    MeasurePreserving (fixedSpatialEmptyCoordinates (X := X)).symm volume volume :=
  fixedSpatialEmptyCoordinates_measurePreserving.symm
    (fixedSpatialEmptyCoordinates (X := X)).toHomeomorph.toMeasurableEquiv

noncomputable def fixedSpatialEmptyDensity (f : (X → ℝ) → ℝ)
    (v : (Σ _ : X, Unit ⊕ Empty) → ℝ) : ℝ :=
  f (fixedSpatialEmptyCoordinates.symm v)

theorem fixedSpatialEmptyDensity_image_law (f : (X → ℝ) → ℝ) :
    Measure.map fixedSpatialEmptyCoordinates (realDensityMeasure volume f) =
      realDensityMeasure volume (fixedSpatialEmptyDensity f) := by
  have h := realDensityMeasure_map_equiv
    (fixedSpatialEmptyCoordinates (X := X)).toHomeomorph.toMeasurableEquiv volume f
  change Measure.map (fixedSpatialEmptyCoordinates (X := X)) (realDensityMeasure volume f) =
    realDensityMeasure (Measure.map (fixedSpatialEmptyCoordinates (X := X)) volume)
      (fixedSpatialEmptyDensity f) at h
  rw [fixedSpatialEmptyCoordinates_measurePreserving.map_eq] at h
  exact h

theorem fixedSpatialEmptyDensity_probability_data (f : (X → ℝ) → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hfi : Integrable f) (hfm : (∫ x, f x) = 1) :
    (∀ v, 0 ≤ fixedSpatialEmptyDensity f v) ∧
      Integrable (fixedSpatialEmptyDensity f) ∧
      (∫ v, fixedSpatialEmptyDensity f v) = 1 := by
  refine ⟨fun v => hf0 _,
    fixedSpatialEmptyCoordinates_symm_measurePreserving.integrable_comp_of_integrable hfi, ?_⟩
  exact (fixedSpatialEmptyCoordinates_symm_measurePreserving.integral_comp
    (fixedSpatialEmptyCoordinates (X := X)).symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding f).trans hfm

theorem fixedSpatialEmptyDensity_bounds (f : (X → ℝ) → ℝ) {C : ℝ} {L : ℝ≥0}
    (hC : ∀ x, f x ∈ Set.Icc (0 : ℝ) C) (hL : LipschitzWith L f) :
    (∀ v, fixedSpatialEmptyDensity f v ∈ Set.Icc (0 : ℝ) C) ∧
      LipschitzWith L (fixedSpatialEmptyDensity f) := by
  refine ⟨fun v => hC _, ?_⟩
  have hi : LipschitzWith 1 (fun v : (Σ _ : X, Unit ⊕ Empty) → ℝ =>
      (fixedSpatialEmptyCoordinates (X := X)).symm v) := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    simp only [NNReal.coe_one, one_mul]
    exact le_of_eq ((fixedSpatialEmptyCoordinates (X := X)).symm.isometry.dist_eq v w)
  apply LipschitzWith.of_dist_le_mul
  intro v w
  exact (hL.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left
    (by simpa only [NNReal.coe_one, one_mul] using hi.dist_le_mul v w) (NNReal.coe_nonneg L))

theorem fixedSpatialEmptyDensity_zero_outside (f : (X → ℝ) → ℝ) {R : ℝ}
    (hf : ∀ x, R < ‖x‖ → f x = 0)
    (v : (Σ _ : X, Unit ⊕ Empty) → ℝ) (hv : R < ‖v‖) :
    fixedSpatialEmptyDensity f v = 0 := by
  apply hf
  simpa only [LinearIsometryEquiv.norm_map] using hv

end Erdos3

end

end OAI
