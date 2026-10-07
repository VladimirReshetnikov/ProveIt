import OAI.Combinatorics.Progressions.Lattices.ResidueAffineProfileLaw

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Matrix

noncomputable def shiftedMatrixCountFactor (I J : Type*) [Fintype I] [Fintype J] : ℝ :=
  (4 * (Fintype.card J : ℝ) + 1) ^ Fintype.card I

theorem shiftedMatrixCountFactor_le_exp (I J : Type*) [Fintype I] [Fintype J] :
    shiftedMatrixCountFactor I J ≤
      Real.exp ((Fintype.card I : ℝ) * (4 * (Fintype.card J : ℝ) + 1)) := by
  unfold shiftedMatrixCountFactor
  calc
    _ ≤ (Real.exp (4 * (Fintype.card J : ℝ) + 1)) ^ Fintype.card I := by
      gcongr
      linarith [Real.add_one_le_exp (4 * (Fintype.card J : ℝ) + 1)]
    _ = _ := (Real.exp_nat_mul _ _).symm

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem shiftedMatrixGridProxy_integrable (M : Matrix I J ℤ) (s : I ↪ J)
    (hM : (M.submatrix id s).det ≠ 0) (a S : J → ℝ) (P : I → ℝ)
    (hS : ∀ j, 0 < S j) (hP : ∀ i, 0 < P i) (ha : ∀ j, |a j| ≤ S j)
    (hentry : ∀ i j, |normalizedIntegerColumns M S P i j| ≤ 1) :
    Integrable (coefficientGridProxy M s hM S P hS hP (shiftedUnitProfile a S)) Measure.count := by
  apply coefficientGridProxy_integrable M s hM S P hS hP _ (shiftedUnitProfile_support a S hS ha)
  exact mul_le_mul_of_nonneg_right
    (normalized_selected_split_norm_le M s S P zero_le_one hentry) (by norm_num : (0 : ℝ) ≤ 2)

theorem shiftedMatrixImage_count_error (M : Matrix I J ℤ) (s : I ↪ J)
    (hM : (M.submatrix id s).det ≠ 0) (a S : J → ℝ) (P : I → ℝ)
    (hS : ∀ j, 0 < S j) (hP : ∀ i, 0 < P i) (hP1 : ∀ i, 1 ≤ P i)
    (ha : ∀ j, |a j| ≤ S j) (hZ : 0 < shiftedSmoothProductMass a S)
    (hentry : ∀ i j, |normalizedIntegerColumns M S P i j| ≤ 1) {ε : ℝ}
    (he : ∀ v, |(∏ i, P i) *
      (((shiftedSmoothProductPMF a S hS hZ).map (fun z => M *ᵥ z)) v).toReal -
      coefficientImageMask M P (selectedCoefficientDensity M s hM S P hS hP (shiftedUnitProfile a S)) v| ≤ ε) :
    (∫ v, |(((shiftedSmoothProductPMF a S hS hZ).map (fun z => M *ᵥ z)) v).toReal -
      coefficientGridProxy M s hM S P hS hP (shiftedUnitProfile a S) v| ∂Measure.count) ≤
      shiftedMatrixCountFactor I J * ε := by
  let f := shiftedUnitProfile a S
  have hs := shiftedUnitProfile_support a S hS ha
  have hz : 0 < coefficientWeightSum f S := by rw [shiftedUnitProfile_mass]; exact hZ
  have hmap : coefficientImagePMF M f (shiftedUnitProfile_nonneg a S) S hS hs hz =
      (shiftedSmoothProductPMF a S hS hZ).map (fun z => M *ᵥ z) := by
    unfold coefficientImagePMF
    rw [coefficientPMF_shiftedUnitProfile a S hS hs hZ]
  have hnorm : ‖matrixSupCLM (normalizedIntegerColumns M S P)‖ ≤ (Fintype.card J : ℝ) := by
    simpa only [mul_one] using matrixSupCLM_norm_le _ zero_le_one hentry
  have hsplit := normalized_selected_split_norm_le M s S P zero_le_one hentry
  have hpoint : ∀ v, |(∏ i, P i) *
      (coefficientImagePMF M f (shiftedUnitProfile_nonneg a S) S hS hs hz v).toReal -
      coefficientImageMask M P (selectedCoefficientDensity M s hM S P hS hP f) v| ≤ ε := by
    simpa only [hmap] using he
  have h := coefficientImage_count_error M s hM S P hS hP hP1 f
    (shiftedUnitProfile_nonneg a S) hs hz (T := (Fintype.card J : ℝ) * 2)
    (by positivity) (mul_le_mul_of_nonneg_right hnorm (by norm_num))
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_right hsplit (by norm_num : (0 : ℝ) ≤ 2)) hpoint
  rw [hmap] at h
  simpa only [shiftedMatrixCountFactor,
    show 2 * ((Fintype.card J : ℝ) * 2) + 1 = 4 * (Fintype.card J : ℝ) + 1 by ring] using h

end Erdos3

end

end OAI
