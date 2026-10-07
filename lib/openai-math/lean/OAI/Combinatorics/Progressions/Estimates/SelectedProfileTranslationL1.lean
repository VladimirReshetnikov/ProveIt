import OAI.Combinatorics.Progressions.Lattices.AffineProfileTranslationL1

namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem selectedCoefficientProfile_translation_l1 {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (f : (J → ℝ) → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hm : ∀ a b, (∫ x, |f (x + a) - f (x + b)|) ≤ D * dist a b)
    (a b : (UnselectedColumn s → ℝ) × (I → ℝ)) :
    (∫ p, |selectedCoefficientProfile s f (p + a) - selectedCoefficientProfile s f (p + b)|) ≤
      D * dist a b := by
  have hadd (u v : (UnselectedColumn s → ℝ) × (I → ℝ)) :
      selectedCoefficientEquiv s ℝ (u + v) =
        selectedCoefficientEquiv s ℝ u + selectedCoefficientEquiv s ℝ v := by
    funext j
    simp only [selectedCoefficientEquiv_apply, Pi.add_apply]
    cases (selectedFreeFirstEquiv s).symm j <;> rfl
  have he : (fun p => |selectedCoefficientProfile s f (p + a) -
      selectedCoefficientProfile s f (p + b)|) = selectedCoefficientProfile s
        (fun x => |f (x + selectedCoefficientEquiv s ℝ a) - f (x + selectedCoefficientEquiv s ℝ b)|) := by
    funext p
    simp only [selectedCoefficientProfile, Function.comp_apply, hadd]
  rw [he, selectedCoefficientProfile_integral]
  apply (hm _ _).trans
  apply mul_le_mul_of_nonneg_left _ hD
  simpa only [NNReal.coe_one, one_mul] using (selectedCoefficientEquiv_lipschitz s).dist_le_mul a b

theorem affineSelectedPivot_translation_l1 {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (UnselectedColumn s → ℝ) →L[ℝ] (I → ℝ))
    (c w : J → ℝ) {δ : ℝ} (hδ : 0 < δ) (hw : ∀ j, δ ≤ w j) (a b : I → ℝ) :
    (∫ v, |pivotOutputDensity A B (selectedCoefficientProfile s (affineProductProfile c w)) (v + a) -
      pivotOutputDensity A B (selectedCoefficientProfile s (affineProductProfile c w)) (v + b)|) ≤
      ((Fintype.card J * (4 * (probabilityProfileLipschitz : ℝ) / δ)) *
        ‖A.symm.toContinuousLinearMap‖) * dist a b := by
  have hi := selectedCoefficientProfile_integrable s
    (affineProductProfile_integrable c w (fun j => hδ.trans_le (hw j)))
  apply (pivotOutputDensity_translation_l1 A B _ hi a b).trans
  have he := selectedCoefficientProfile_translation_l1 s (affineProductProfile c w)
    (D := Fintype.card J * (4 * (probabilityProfileLipschitz : ℝ) / δ))
    (by positivity) (affineProductProfile_translation_l1 c w hδ hw)
    (0, A.symm a) (0, A.symm b)
  apply he.trans
  have hd : dist (A.symm a) (A.symm b) ≤ ‖A.symm.toContinuousLinearMap‖ * dist a b := by
    rw [dist_eq_norm, ← map_sub, dist_eq_norm]
    exact A.symm.toContinuousLinearMap.le_opNorm _
  simp only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
  exact (mul_le_mul_of_nonneg_left hd (by positivity)).trans_eq (by ring)

end Erdos3

end

end OAI
