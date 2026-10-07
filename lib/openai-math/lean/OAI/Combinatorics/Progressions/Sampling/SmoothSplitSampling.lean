import OAI.Combinatorics.Progressions.Estimates.SelectedCoefficientEvaluation
import OAI.Combinatorics.Progressions.Probability.ScaledInputProbability

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

noncomputable def smoothSampleSum (S : ℝ) : ℝ :=
  ∑' k : ℤ, smoothProbabilityProfile ((k : ℝ) / S)

theorem smoothProfileSamples_summable {S : ℝ} (hS : 0 < S) :
    Summable (fun k : ℤ => smoothProbabilityProfile ((k : ℝ) / S)) := by
  have h : Summable (sampledWeight smoothProbabilityProfile 0 S) :=
    (hasSum_sum_of_ne_finset_zero (sampledWeight_zero_off_indices smoothProbabilityProfile
      (a := 0) hS smoothProbabilityProfile_zero_outside)).summable
  change Summable (fun k : ℤ => smoothProbabilityProfile (((k : ℝ) - 0) / S)) at h
  simpa only [sub_zero] using h

theorem smoothSampleSum_pos {S : ℝ} (hS : 0 < S) : 0 < smoothSampleSum S := by
  have h := (smoothProfileSamples_summable hS).le_tsum 0
    (fun k _ => (smoothProbabilityProfile_range _).1)
  simp only [Int.cast_zero, zero_div] at h
  exact smoothProbabilityProfile_pos_zero.trans_le h

theorem smoothSampleSum_error {S : ℝ} (hS : 1 ≤ S) :
    |smoothSampleSum S / S - 1| ≤ 4 * (probabilityProfileLipschitz : ℝ) / S := by
  have h := sampledWeightSum_error smoothProbabilityProfile smoothProbabilityProfile_lipschitz
    (a := 0) zero_le_one hS smoothProbabilityProfile_zero_outside
  rw [sampledWeightSum_eq_tsum _ (zero_lt_one.trans_le hS)
    smoothProbabilityProfile_zero_outside] at h
  simpa only [sub_zero, smoothSampleSum, smoothProbabilityProfile_integral,
    show (2 : ℝ) * 1 + 2 = 4 by norm_num] using h

noncomputable def smoothCoefficientPMF (S : ℝ) (hS : 0 < S) : PMF ℤ :=
  realWeightPMF (fun k => smoothProbabilityProfile ((k : ℝ) / S))
    (fun _ => (smoothProbabilityProfile_range _).1)
    (smoothProfileSamples_summable hS) (smoothSampleSum_pos hS)

theorem smoothCoefficientPMF_apply (S : ℝ) (hS : 0 < S) (k : ℤ) :
    (smoothCoefficientPMF S hS k).toReal = smoothProbabilityProfile ((k : ℝ) / S) / smoothSampleSum S :=
  realWeightPMF_apply _ _ _ _ k

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem smoothProductSamples_summable {I : Type*} [Fintype I]
    (S : I → ℝ) (hS : ∀ i, 0 < S i) :
    Summable (fun z : I → ℤ => smoothProductProfile I (fun i => (z i : ℝ) / S i)) := by
  have h := rectangularWeight_summable (smoothProductProfile I) (fun _ => 0) S hS
    (smoothProductProfile_zero_outside I)
  change Summable (fun z : I → ℤ =>
    smoothProductProfile I (fun i => ((z i : ℝ) - 0) / S i)) at h
  simpa only [sub_zero] using h

theorem smoothProductSamples_sum {I : Type*} [Fintype I]
    (S : I → ℝ) (hS : ∀ i, 0 < S i) :
    (∑' z : I → ℤ, smoothProductProfile I (fun i => (z i : ℝ) / S i)) =
      ∏ i, smoothSampleSum (S i) := by
  classical
  have h := rectangularWeightSum_eq_tsum (smoothProductProfile I) (fun _ => 0) S hS
    (smoothProductProfile_zero_outside I)
  change rectangularWeightSum (smoothProductProfile I) (fun _ => 0) S 1 =
    ∑' z : I → ℤ, smoothProductProfile I (fun i => ((z i : ℝ) - 0) / S i) at h
  simp only [sub_zero] at h
  rw [← h]
  simp only [rectangularWeightSum, rectangularWeightIndices, rectangularWeight,
    rectangularLatticePoint, sub_zero, smoothProductProfile]
  rw [← Finset.prod_univ_sum (fun i => sampledWeightIndices 0 (S i) 1)
    (fun i k => smoothProbabilityProfile ((k : ℝ) / S i))]
  apply Finset.prod_congr rfl
  intro i _
  have hi := sampledWeightSum_eq_tsum smoothProbabilityProfile (a := 0) (hS i)
    smoothProbabilityProfile_zero_outside
  simpa only [sampledWeightSum, sampledWeight, sub_zero, smoothSampleSum] using hi

theorem smoothProductSamples_sum_pos {I : Type*} [Fintype I]
    (S : I → ℝ) (hS : ∀ i, 0 < S i) :
    0 < ∑' z : I → ℤ, smoothProductProfile I (fun i => (z i : ℝ) / S i) := by
  rw [smoothProductSamples_sum S hS]
  exact Finset.prod_pos (fun i _ => smoothSampleSum_pos (hS i))

noncomputable def smoothProductPMF {I : Type*} [Fintype I]
    (S : I → ℝ) (hS : ∀ i, 0 < S i) : PMF (I → ℤ) :=
  realWeightPMF (fun z => smoothProductProfile I (fun i => (z i : ℝ) / S i))
    (fun _ => (smoothProductProfile_range I _).1)
    (smoothProductSamples_summable S hS) (smoothProductSamples_sum_pos S hS)

theorem smoothProductPMF_apply {I : Type*} [Fintype I]
    (S : I → ℝ) (hS : ∀ i, 0 < S i) (z : I → ℤ) :
    (smoothProductPMF S hS z).toReal = ∏ i, (smoothCoefficientPMF (S i) (hS i) (z i)).toReal := by
  rw [smoothProductPMF, realWeightPMF_apply, smoothProductSamples_sum S hS]
  simp only [smoothProductProfile, smoothCoefficientPMF_apply, Finset.prod_div_distrib]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def shiftedSmoothSampleSum (a S : ℝ) : ℝ :=
  ∑' k : ℤ, smoothProbabilityProfile (((k : ℝ) - a) / S)

theorem shiftedSmoothSamples_summable (a : ℝ) {S : ℝ} (hS : 0 < S) :
    Summable (fun k : ℤ => smoothProbabilityProfile (((k : ℝ) - a) / S)) :=
  (hasSum_sum_of_ne_finset_zero (sampledWeight_zero_off_indices smoothProbabilityProfile
    (a := a) hS smoothProbabilityProfile_zero_outside)).summable

theorem shiftedSmoothSampleSum_error (a : ℝ) {S : ℝ} (hS : 1 ≤ S) :
    |shiftedSmoothSampleSum a S / S - 1| ≤ 4 * (probabilityProfileLipschitz : ℝ) / S := by
  have he := sampledWeightSum_error smoothProbabilityProfile smoothProbabilityProfile_lipschitz
    (a := a) zero_le_one hS smoothProbabilityProfile_zero_outside
  rw [sampledWeightSum_eq_tsum _ (zero_lt_one.trans_le hS) smoothProbabilityProfile_zero_outside] at he
  simpa only [shiftedSmoothSampleSum, smoothProbabilityProfile_integral,
    show (2 : ℝ) * 1 + 2 = 4 by norm_num] using he

theorem shiftedSmoothSampleSum_pos (a : ℝ) {S : ℝ}
    (hS : 8 * (probabilityProfileLipschitz : ℝ) ≤ S) : 0 < shiftedSmoothSampleSum a S := by
  have hA : (1 : ℝ) ≤ probabilityProfileLipschitz := probabilityProfileLipschitz_one_le
  have hS1 : 1 ≤ S := by linarith
  have he := shiftedSmoothSampleSum_error a hS1
  have hsmall : 4 * (probabilityProfileLipschitz : ℝ) / S ≤ 1 / 2 :=
    (div_le_iff₀ (zero_lt_one.trans_le hS1)).mpr (by linarith)
  have hlo := (abs_le.mp (he.trans hsmall)).1
  have hpos : 0 < shiftedSmoothSampleSum a S / S := by linarith
  rcases div_pos_iff.mp hpos with h | h
  · exact h.1
  · linarith [h.2]

noncomputable def shiftedSmoothCoefficientPMF (a S : ℝ) (hS : 0 < S)
    (hZ : 0 < shiftedSmoothSampleSum a S) : PMF ℤ :=
  realWeightPMF (fun k => smoothProbabilityProfile (((k : ℝ) - a) / S))
    (fun _ => (smoothProbabilityProfile_range _).1) (shiftedSmoothSamples_summable a hS) hZ

theorem shiftedSmoothCoefficientPMF_apply (a S : ℝ) (hS : 0 < S)
    (hZ : 0 < shiftedSmoothSampleSum a S) (k : ℤ) :
    (shiftedSmoothCoefficientPMF a S hS hZ k).toReal =
      smoothProbabilityProfile (((k : ℝ) - a) / S) / shiftedSmoothSampleSum a S :=
  realWeightPMF_apply _ _ _ _ k

theorem shiftedSmoothProductSamples_sum {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) :
    (∑' z : I → ℤ, smoothProductProfile I (fun i => ((z i : ℝ) - a i) / S i)) =
      ∏ i, shiftedSmoothSampleSum (a i) (S i) := by
  classical
  have he := rectangularWeightSum_eq_tsum (smoothProductProfile I) a S hS
    (smoothProductProfile_zero_outside I)
  change rectangularWeightSum (smoothProductProfile I) a S 1 =
    ∑' z : I → ℤ, smoothProductProfile I (fun i => ((z i : ℝ) - a i) / S i) at he
  rw [← he]
  simp only [rectangularWeightSum, rectangularWeightIndices, rectangularWeight,
    rectangularLatticePoint, smoothProductProfile]
  rw [← Finset.prod_univ_sum (fun i => sampledWeightIndices (a i) (S i) 1)
    (fun i k => smoothProbabilityProfile (((k : ℝ) - a i) / S i))]
  apply Finset.prod_congr rfl
  intro i _
  have hi := sampledWeightSum_eq_tsum smoothProbabilityProfile (a := a i) (hS i)
    smoothProbabilityProfile_zero_outside
  exact hi

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem scaledInputWeightSum_splitSmoothProductProfile {I J : Type*}
    [Fintype I] [Fintype J] (S : I → ℝ) (T : J → ℝ)
    (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j) :
    scaledInputWeightSum (splitSmoothProductProfile J I) S T =
      (∏ i, smoothSampleSum (S i)) * ∏ j, smoothSampleSum (T j) := by
  have hscale : ∀ k, 0 < Sum.elim T S k := by intro k; cases k <;> simp [hS, hT]
  unfold scaledInputWeightSum
  rw [← splitInputProfile_sample_sum, splitSmoothProductProfile_join,
    smoothProductSamples_sum _ hscale]
  simp [Fintype.prod_sum_type, mul_comm]

theorem scaledInputMass_splitSmoothProductProfile_pos {I J : Type*}
    [Fintype I] [Fintype J] (S : I → ℝ) (T : J → ℝ)
    (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j) :
    0 < scaledInputMass (splitSmoothProductProfile J I) S T := by
  rw [scaledInputMass, scaledInputWeightSum_splitSmoothProductProfile S T hS hT]
  exact div_pos
    (mul_pos (Finset.prod_pos (fun i _ => smoothSampleSum_pos (hS i)))
      (Finset.prod_pos (fun j _ => smoothSampleSum_pos (hT j))))
    (mul_pos (Finset.prod_pos (fun i _ => hS i)) (Finset.prod_pos (fun j _ => hT j)))

theorem scaledInputPMF_splitSmoothProductProfile {I J : Type*}
    [Fintype I] [Fintype J] (S : I → ℝ) (T : J → ℝ)
    (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j)
    (hM : 0 < scaledInputMass (splitSmoothProductProfile J I) S T)
    (p : (I → ℤ) × (J → ℤ)) :
    (scaledInputPMF (splitSmoothProductProfile J I) (fun z => (splitSmoothProductProfile_range J I z).1)
      S T hS hT (splitSmoothProductProfile_zero_outside J I) hM p).toReal =
      (smoothProductPMF S hS p.1).toReal * (smoothProductPMF T hT p.2).toReal := by
  rw [scaledInputPMF_apply, scaledInputWeightSum_splitSmoothProductProfile S T hS hT]
  simp only [smoothProductPMF, realWeightPMF_apply, smoothProductSamples_sum S hS,
    smoothProductSamples_sum T hT,
    scaledIntegerWeight, splitSmoothProductProfile]
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem splitInputProfile_smooth (J I : Type*) [Fintype J] [Fintype I] :
    splitInputProfile (smoothSplitProfile J I) = smoothProductProfile (J ⊕ I) := by
  funext x
  unfold splitInputProfile
  rw [smoothSplitProfile_join]
  congr 1
  funext k
  cases k <;> rfl

theorem smoothSplit_weight_sum {I J : Type*} [Fintype I] [Fintype J]
    (S : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j) :
    scaledInputWeightSum (smoothSplitProfile J I) S T =
      (∏ i, smoothSampleSum (S i)) * (∏ j, smoothSampleSum (T j)) := by
  have hST : ∀ k, 0 < Sum.elim T S k := by
    intro k
    cases k with
    | inl j => exact hT j
    | inr i => exact hS i
  unfold scaledInputWeightSum
  rw [← splitInputProfile_sample_sum, splitInputProfile_smooth,
    smoothProductSamples_sum _ hST]
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, mul_comm]

theorem smoothSplit_mass_pos {I J : Type*} [Fintype I] [Fintype J]
    (S : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j) :
    0 < scaledInputMass (smoothSplitProfile J I) S T := by
  rw [scaledInputMass, smoothSplit_weight_sum S T hS hT]
  exact div_pos
    (mul_pos (Finset.prod_pos (fun i _ => smoothSampleSum_pos (hS i)))
      (Finset.prod_pos (fun j _ => smoothSampleSum_pos (hT j))))
    (mul_pos (Finset.prod_pos (fun i _ => hS i)) (Finset.prod_pos (fun j _ => hT j)))

theorem smoothSplit_mass_product {I J : Type*} [Fintype I] [Fintype J]
    (S : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j) :
    scaledInputMass (smoothSplitProfile J I) S T =
      (∏ i, smoothSampleSum (S i) / S i) * (∏ j, smoothSampleSum (T j) / T j) := by
  rw [scaledInputMass, smoothSplit_weight_sum S T hS hT]
  simp only [Finset.prod_div_distrib, div_mul_div_comm]

theorem smoothSplit_inputPMF_apply {I J : Type*} [Fintype I] [Fintype J]
    (S : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j)
    (p : (I → ℤ) × (J → ℤ)) :
    (scaledInputPMF (smoothSplitProfile J I) (fun p => (smoothSplitProfile_range J I p).1)
      S T hS hT (smoothSplitProfile_zero_outside J I) (smoothSplit_mass_pos S T hS hT) p).toReal =
      (∏ i, (smoothCoefficientPMF (S i) (hS i) (p.1 i)).toReal) *
        (∏ j, (smoothCoefficientPMF (T j) (hT j) (p.2 j)).toReal) := by
  rw [scaledInputPMF_apply, smoothSplit_weight_sum S T hS hT]
  simp only [scaledIntegerWeight, smoothSplitProfile, smoothProductProfile,
    smoothCoefficientPMF_apply, Finset.prod_div_distrib, div_mul_div_comm]
  rw [mul_comm (∏ j, smoothProbabilityProfile ((p.2 j : ℝ) / T j))]

end Erdos3

end

end OAI
