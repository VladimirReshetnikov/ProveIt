import OAI.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (j : Fin m) (i : Fin (n j)) (hσ1 : σ j ≤ 1)
variable (henormous : S.value ^ (layerTailDegree m + 1) < basisAxisScale (basis j) i)

theorem allocatedEnormousProfile_support
    (z : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (hz : z ∈ (allocatedEnormousProfilePMF B U basis hR hσ S j i hσ1 henormous).support) :
    affineProductProfile (allocatedIntegerProfileCenters B R j i)
      (allocatedIntegerProfileWidths B R σ j i)
      (fun e => (z e : ℝ) / allocatedIntegerProfileScales B U basis S j i e) ≠ 0 := by
  have hpos := ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp hz)
    (PMF.apply_ne_top _ _)
  rw [allocatedEnormousProfilePMF, coefficientPMF_apply] at hpos
  change 0 < affineProductProfile (allocatedIntegerProfileCenters B R j i)
      (allocatedIntegerProfileWidths B R σ j i)
      (fun e => (z e : ℝ) / allocatedIntegerProfileScales B U basis S j i e) / _ at hpos
  intro hzero
  rw [hzero, zero_div] at hpos
  exact (lt_irrefl 0) hpos

include hσ1 henormous in
theorem allocatedEnormousProfile_support_of_coordinate_support
    (z : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (hz : ∀ e, z e ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i e).support) :
    affineProductProfile (allocatedIntegerProfileCenters B R j i)
      (allocatedIntegerProfileWidths B R σ j i)
      (fun e => (z e : ℝ) / allocatedIntegerProfileScales B U basis S j i e) ≠ 0 := by
  classical
  let p := independentProductPMF (allocatedLayerIntegerPMFs B U basis hR hσ S j i)
  have hp : p = allocatedEnormousProfilePMF B U basis hR hσ S j i hσ1 henormous := by
    apply PMF.toMeasure_injective
    change (Measure.pi (fun e =>
      (allocatedLayerIntegerPMFs B U basis hR hσ S j i e).toMeasure)).toPMF.toMeasure = _
    rw [Measure.toPMF_toMeasure]
    exact allocatedEnormous_coefficient_law B U basis hR hσ S j i hσ1 henormous
  apply allocatedEnormousProfile_support B U basis hR hσ S j i hσ1 henormous z
  rw [← hp, PMF.mem_support_iff]
  change independentProductPMF _ z ≠ 0
  rw [independentProductPMF_apply]
  exact Finset.prod_ne_zero_iff.mpr (fun e _ => (PMF.mem_support_iff _ _).mp (hz e))

end Erdos3.VectorPolynomial

end

end OAI
