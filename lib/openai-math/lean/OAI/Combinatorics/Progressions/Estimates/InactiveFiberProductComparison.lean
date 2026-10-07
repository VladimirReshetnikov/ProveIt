import OAI.Combinatorics.Progressions.Estimates.FiniteFiberTest

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {I Z : Type*} [Fintype I]

theorem fiberMean_mul_bounds_of_abs_sub_one_le
    (law : FiniteProbabilityWeights I) (gridPoint : I → Z) (z : Z)
    (V δ : ℝ) (hV : 0 ≤ V) (base omitted : I → ℝ)
    (hbase : ∀ i, 0 ≤ base i) (homitted : ∀ i, |omitted i - 1| ≤ δ) :
    (1 - δ) * (V * law.fiberMean gridPoint z base) ≤
        V * law.fiberMean gridPoint z (fun i => base i * omitted i) ∧
      V * law.fiberMean gridPoint z (fun i => base i * omitted i) ≤
        (1 + δ) * (V * law.fiberMean gridPoint z base) := by
  classical
  have hpoint (i : I) :
      (1 - δ) * base i ≤ base i * omitted i ∧
        base i * omitted i ≤ (1 + δ) * base i := by
    have herr := abs_le.mp (homitted i)
    constructor
    · have hlow : 1 - δ ≤ omitted i := by linarith [herr.1]
      simpa only [mul_comm (base i)] using mul_le_mul_of_nonneg_right hlow (hbase i)
    · have hupp : omitted i ≤ 1 + δ := by linarith [herr.2]
      simpa only [mul_comm (base i)] using mul_le_mul_of_nonneg_right hupp (hbase i)
  have hlower : (1 - δ) * law.fiberMean gridPoint z base ≤
      law.fiberMean gridPoint z (fun i => base i * omitted i) := by
    unfold fiberMean
    rw [← law.mean_const_mul]
    apply law.mean_mono
    intro i
    by_cases hi : gridPoint i = z
    · simpa only [hi, ite_true] using (hpoint i).1
    · simp only [hi, ite_false, mul_zero, le_refl]
  have hupper : law.fiberMean gridPoint z (fun i => base i * omitted i) ≤
      (1 + δ) * law.fiberMean gridPoint z base := by
    unfold fiberMean
    rw [← law.mean_const_mul]
    apply law.mean_mono
    intro i
    by_cases hi : gridPoint i = z
    · simpa only [hi, ite_true] using (hpoint i).2
    · simp only [hi, ite_false, mul_zero, le_refl]
  constructor
  · simpa only [mul_left_comm V (1 - δ)] using
      mul_le_mul_of_nonneg_left hlower hV
  · simpa only [mul_left_comm V (1 + δ)] using
      mul_le_mul_of_nonneg_left hupper hV

theorem fiberMean_prod_bounds_of_omitted_prod_sub_one_le
    {L : Type*} [Fintype L] [DecidableEq L]
    (law : FiniteProbabilityWeights I) (gridPoint : I → Z) (z : Z)
    (V δ : ℝ) (hV : 0 ≤ V) (_hδ : 0 ≤ δ)
    (retained : Finset L) (f : I → L → ℝ)
    (hf : ∀ i l, 0 ≤ f i l)
    (homitted : ∀ i, |(∏ l ∈ Finset.univ \ retained, f i l) - 1| ≤ δ) :
    (1 - δ) * (V * law.fiberMean gridPoint z (fun i => ∏ l ∈ retained, f i l)) ≤
        V * law.fiberMean gridPoint z (fun i => ∏ l, f i l) ∧
      V * law.fiberMean gridPoint z (fun i => ∏ l, f i l) ≤
        (1 + δ) * (V * law.fiberMean gridPoint z (fun i => ∏ l ∈ retained, f i l)) := by
  have hsplit (i : I) : (∏ l ∈ retained, f i l) *
      (∏ l ∈ Finset.univ \ retained, f i l) = ∏ l, f i l := by
    simpa only [Finset.compl_eq_univ_sdiff] using
      Finset.prod_mul_prod_compl retained (f i)
  simpa only [hsplit] using
    law.fiberMean_mul_bounds_of_abs_sub_one_le gridPoint z V δ hV
      (fun i => ∏ l ∈ retained, f i l)
      (fun i => ∏ l ∈ Finset.univ \ retained, f i l)
      (fun i => Finset.prod_nonneg (fun l _ => hf i l)) homitted

end Erdos3.FiniteProbabilityWeights

end

end OAI
