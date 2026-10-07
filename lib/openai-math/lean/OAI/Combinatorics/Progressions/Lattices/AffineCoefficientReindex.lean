import OAI.Combinatorics.Progressions.Probability.CoefficientJetDensityFactors

namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

variable {I J O : Type*} [Fintype I] [Fintype J]

theorem affineProductProfile_reindex (e : I ≃ J) (c w x : J → ℝ) :
    affineProductProfile (c ∘ e) (w ∘ e) (x ∘ e) = affineProductProfile c w x :=
  Equiv.prod_comp e (fun j => affineProbabilityProfile (c j) (w j) (x j))

theorem affineCoefficientWeight_reindex (e : I ≃ J) (c w S : J → ℝ) (z : J → ℤ) :
    coefficientWeight (affineProductProfile (c ∘ e) (w ∘ e)) (S ∘ e) (z ∘ e) =
      coefficientWeight (affineProductProfile c w) S z :=
  affineProductProfile_reindex e c w (fun j => (z j : ℝ)/S j)

theorem affineCoefficientWeightSum_reindex (e : I ≃ J) (c w S : J → ℝ) :
    coefficientWeightSum (affineProductProfile (c ∘ e) (w ∘ e)) (S ∘ e) =
      coefficientWeightSum (affineProductProfile c w) S := by
  let E : (J → ℤ) ≃ (I → ℤ) := Equiv.arrowCongr e.symm (Equiv.refl ℤ)
  calc
    _ = ∑' z : J → ℤ,
        coefficientWeight (affineProductProfile (c ∘ e) (w ∘ e)) (S ∘ e) (z ∘ e) :=
      (E.tsum_eq _).symm
    _ = _ := tsum_congr (fun z => affineCoefficientWeight_reindex e c w S z)

theorem coefficientPMF_affine_reindex (e : I ≃ J) (c w S : J → ℝ)
    (hw : ∀ j, 0 < w j) (hS : ∀ j, 0 < S j) {R : ℝ} (hR : 0 ≤ R)
    (hcw : ∀ j, |c j|+w j ≤ R) (hZ : 0 < coefficientWeightSum (affineProductProfile c w) S) :
    (coefficientPMF (affineProductProfile (c ∘ e) (w ∘ e))
      (affineProductProfile_nonneg _ _ (fun i => hw (e i))) (S ∘ e) (fun i => hS (e i))
      (affineProductProfile_zero_outside _ _ (fun i => hw (e i)) hR (fun i => hcw (e i)))
      (by rw [affineCoefficientWeightSum_reindex]; exact hZ)).map (fun z => z ∘ e.symm) =
    coefficientPMF (affineProductProfile c w) (affineProductProfile_nonneg c w hw) S hS
      (affineProductProfile_zero_outside c w hw hR hcw) hZ := by
  let E : (I → ℤ) ≃ (J → ℤ) := Equiv.arrowCongr e (Equiv.refl ℤ)
  change (coefficientPMF _ _ _ _ _ _).map E = _
  ext z
  rw [pmf_map_equiv_apply]
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  change ((coefficientPMF _ _ _ _ _ _) (z ∘ e)).toReal = _
  rw [coefficientPMF_apply, coefficientPMF_apply,
    affineCoefficientWeight_reindex, affineCoefficientWeightSum_reindex]

theorem coefficientImagePMF_affine_reindex (A : Matrix O J ℤ) (e : I ≃ J) (c w S : J → ℝ)
    (hw : ∀ j, 0 < w j) (hS : ∀ j, 0 < S j) {R : ℝ} (hR : 0 ≤ R)
    (hcw : ∀ j, |c j|+w j ≤ R) (hZ : 0 < coefficientWeightSum (affineProductProfile c w) S) :
    coefficientImagePMF (A.submatrix id e) (affineProductProfile (c ∘ e) (w ∘ e))
      (affineProductProfile_nonneg _ _ (fun i => hw (e i))) (S ∘ e) (fun i => hS (e i))
      (affineProductProfile_zero_outside _ _ (fun i => hw (e i)) hR (fun i => hcw (e i)))
      (by rw [affineCoefficientWeightSum_reindex]; exact hZ) =
    coefficientImagePMF A (affineProductProfile c w) (affineProductProfile_nonneg c w hw) S hS
      (affineProductProfile_zero_outside c w hw hR hcw) hZ := by
  unfold coefficientImagePMF
  rw [← coefficientPMF_affine_reindex e c w S hw hS hR hcw hZ, PMF.map_comp]
  congr 1
  funext z
  exact Matrix.submatrix_mulVec_equiv A z id e

end Erdos3

end

end OAI
