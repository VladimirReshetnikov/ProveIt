import OAI.Combinatorics.Progressions.Probability.NormalizedJetDensitySupport

namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem splitPivotDensity_parameter_l1 {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (B : (J → ℝ) →L[ℝ] (I → ℝ))
    (C E : (N → ℝ) →L[ℝ] (I → ℝ))
    {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ}
    (hf : Continuous f) (hg : Continuous g) {R S D : ℝ} (hD : 0 ≤ D)
    (hfs : ∀ p, R < ‖p‖ → f p = 0) (hgs : ∀ n, S < ‖n‖ → g n = 0)
    (hf0 : ∀ p, 0 ≤ f p) (hg0 : ∀ n, 0 ≤ g n)
    (hf1 : (∫ p, f p) = 1) (hg1 : (∫ n, g n) = 1)
    (htrans : ∀ a b, (∫ v, |pivotOutputDensity A B f (v + a) -
      pivotOutputDensity A B f (v + b)|) ≤ D * dist a b) :
    (∫ v, |pivotOutputDensity A (splitFreeColumns B C) (splitFreeProfile f g) v -
      pivotOutputDensity A (splitFreeColumns B E) (splitFreeProfile f g) v|) ≤ D * (‖C - E‖ * S) := by
  have hfi : Integrable f := hf.integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_closedBall 0 R) (fun p hp => hfs p (by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hp)))
  have hgi := compactBox_integrable g hg S hgs
  let μ := realDensityMeasure volume g
  let : IsProbabilityMeasure μ := realDensityMeasure_probability volume g hgi hg0 hg1
  have hs : ∀ᵐ n ∂μ, ‖n‖ ≤ S :=
    ae_realDensityMeasure_of_forall_nonzero volume g hg.measurable _
      (fun n hn => le_of_not_gt (fun h => hn (hgs n h)))
  have he := translatedMixture_l1 μ (pivotOutputDensity A B f)
    (pivotOutputDensity_measurable A B hf.measurable) (pivotOutputDensity_nonneg A B hf0)
    (pivotOutputDensity_integrable A B hfi) ((pivotOutputDensity_integral A B hfi).trans hf1)
    hD htrans (fun n => -(C n)) (fun n => -(E n)) C.continuous.measurable.neg
    E.continuous.measurable.neg (δ := ‖C - E‖ * S) (by
      filter_upwards [hs] with n hn
      rw [dist_neg_neg, dist_eq_norm]
      exact ((C - E).le_opNorm n).trans (mul_le_mul_of_nonneg_left hn (norm_nonneg _)))
  simpa only [μ, realDensityMeasure_integral volume g hg.measurable hg0, ← sub_eq_add_neg,
    ← splitPivotDensity_formula A B C hf hg hfs hgs,
    ← splitPivotDensity_formula A B E hf hg hfs hgs] using he

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem normalizedJetDensity_l1_regular {Z P K α I J N : Type*}
    [Fintype P] [DecidableEq P] [Fintype α] [DecidableEq α] [Fintype I] [Fintype J] [Fintype N]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (F : (J → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ P) (z : Z → ℝ) (hz : ∀ j, |z j| ≤ 1)
    (rows : I → Finset α) {degree : ℕ} (hd : ∀ n, (e n).sum (fun _ k => k) ≤ degree)
    {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ}
    (hf : Continuous f) (hg : Continuous g) (R S D : ℝ≥0)
    (hfs : ∀ u, (R : ℝ) < ‖u‖ → f u = 0) (hgs : ∀ n, (S : ℝ) < ‖n‖ → g n = 0)
    (hf0 : ∀ u, 0 ≤ f u) (hg0 : ∀ n, 0 ≤ g n)
    (hf1 : (∫ u, f u) = 1) (hg1 : (∫ n, g n) = 1)
    (htrans : ∀ a b, (∫ v, |pivotOutputDensity A F f (v + a) -
      pivotOutputDensity A F f (v + b)|) ≤ D * dist a b)
    (a : P → ℝ) (ha : a ∈ Metric.closedBall 0 1) (b : P → ℝ) (hb : b ∈ Metric.closedBall 0 1) :
    (∫ v, |normalizedJetDensity A F e input z rows f g a v -
      normalizedJetDensity A F e input z rows f g b v|) ≤
      ((D * (Fintype.card N * polynomialBoxLip (Fintype.card P) degree
        (normalizedJetMass α degree)) * S : ℝ≥0) : ℝ) * dist a b := by
  have he := splitPivotDensity_parameter_l1 A F
    (polynomialColumns (fun o n => normalizedJetColumn (e n) input z (rows o)) a)
    (polynomialColumns (fun o n => normalizedJetColumn (e n) input z (rows o)) b)
    hf hg D.coe_nonneg hfs hgs hf0 hg0 hf1 hg1 htrans
  apply he.trans
  have hc := (normalizedJetColumns_lipschitzOn_box e input z hz rows hd).dist_le_mul a ha b hb
  rw [dist_eq_norm] at hc
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc S.coe_nonneg) D.coe_nonneg).trans_eq
  simp only [NNReal.coe_mul]
  ring

end Erdos3

end

end OAI
