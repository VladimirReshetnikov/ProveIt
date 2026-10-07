import OAI.Combinatorics.Progressions.Estimates.FiniteFiberTest

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

noncomputable def reweight {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (htotal : p.mean w = 1) : FiniteProbabilityWeights X where
  weight x := p.weight x * w x
  nonneg x := mul_nonneg (p.nonneg x) (hw x)
  total := htotal

theorem reweight_complexMean {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (htotal : p.mean w = 1) (F : X → ℂ) :
    (p.reweight w hw htotal).complexMean F = p.complexMean (fun x => (w x : ℂ) * F x) := by
  simp only [complexMean, reweight, Complex.ofReal_mul, mul_assoc]

theorem pi_reweight_complexMean {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] (p : ∀ j, FiniteProbabilityWeights (X j))
    (w : ∀ j, X j → ℝ) (hw : ∀ j x, 0 ≤ w j x) (htotal : ∀ j, (p j).mean (w j) = 1)
    (F : (∀ j, X j) → ℂ) :
    (pi (fun j => (p j).reweight (w j) (hw j) (htotal j))).complexMean F =
      (pi p).complexMean (fun x => ((∏ j, w j (x j) : ℝ) : ℂ) * F x) := by
  change (∑ x, ((∏ j, (p j).weight (x j) * w j (x j) : ℝ) : ℂ) * F x) =
    ∑ x, ((∏ j, (p j).weight (x j) : ℝ) : ℂ) * (((∏ j, w j (x j) : ℝ) : ℂ) * F x)
  simp only [Finset.prod_mul_distrib, Complex.ofReal_mul, mul_assoc]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped NNReal BigOperators

theorem finite_mean_div_self {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (f : X → ℝ) (hf : p.mean f ≠ 0) : p.mean (fun x => f x / p.mean f) = 1 := by
  unfold FiniteProbabilityWeights.mean
  simp only [← mul_div_assoc, ← Finset.sum_div]
  exact div_self hf

theorem normalized_weight_range {E : Type*} (w : E → ℝ) {B Z : ℝ}
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hZ : 1 / 2 ≤ Z) (x : E) :
    0 ≤ w x / Z ∧ w x / Z ≤ 2 * B := by
  have hZ0 : 0 < Z := by linarith
  have hB : 0 ≤ B := (hw x).1.trans (hw x).2
  refine ⟨div_nonneg (hw x).1 hZ0.le, (div_le_iff₀ hZ0).mpr ?_⟩
  nlinarith [(hw x).2]

theorem normalized_weight_lipschitz {E : Type*} [PseudoMetricSpace E]
    (w : E → ℝ) {K : ℝ≥0} (hw : LipschitzWith K w) {Z : ℝ} (hZ : 1 / 2 ≤ Z) :
    LipschitzWith (2 * K) (fun x => w x / Z) := by
  have hZ0 : 0 < Z := by linarith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hZ0]
  have hxy := hw.dist_le_mul x y
  rw [Real.dist_eq] at hxy
  apply (div_le_iff₀ hZ0).mpr
  have hnonneg : 0 ≤ (K : ℝ) * dist x y := mul_nonneg K.coe_nonneg dist_nonneg
  simp only [NNReal.coe_mul, NNReal.coe_ofNat]
  nlinarith

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

noncomputable def lowWeightFibers {X R : Type*} [Fintype X] [Fintype R]
    (p : FiniteProbabilityWeights X) (F : X → R) (w : X → ℝ) (η : ℝ) : Finset R :=
  Finset.univ.filter (fun r => p.fiberMean F r w < η * (p.fiberLaw F).weight r)

theorem lowWeightFibers_weighted_mass {X R : Type*} [Fintype X] [Fintype R]
    (p : FiniteProbabilityWeights X) (F : X → R) (w : X → ℝ) {η : ℝ} (hη : 0 ≤ η) :
    (∑ r ∈ p.lowWeightFibers F w η, p.fiberMean F r w) ≤ η := by
  calc
    _ ≤ ∑ r ∈ p.lowWeightFibers F w η, η * (p.fiberLaw F).weight r :=
      Finset.sum_le_sum (fun r hr => (Finset.mem_filter.mp hr).2.le)
    _ = η * (p.fiberLaw F).mass (p.lowWeightFibers F w η) := by rw [mass, Finset.mul_sum]
    _ ≤ η * 1 := mul_le_mul_of_nonneg_left ((p.fiberLaw F).mass_le_one _) hη
    _ = η := mul_one _

theorem retained_fiber_weight_mean_ge {X R : Type*} [Fintype X] [Fintype R]
    (p : FiniteProbabilityWeights X) (F : X → R) (w : X → ℝ) (η : ℝ) (r : R)
    (hr : r ∉ p.lowWeightFibers F w η) (hbase : 0 < (p.fiberLaw F).weight r) :
    η ≤ p.fiberMean F r w / (p.fiberLaw F).weight r := by
  apply (le_div_iff₀ hbase).mpr
  apply le_of_not_gt
  intro h
  exact hr (Finset.mem_filter.mpr ⟨Finset.mem_univ r, h⟩)

theorem reweight_fiberLaw_weight {X R : Type*} [Fintype X] [Fintype R]
    (p : FiniteProbabilityWeights X) (F : X → R) (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hmean : p.mean w = 1) (r : R) :
    ((p.reweight w hw hmean).fiberLaw F).weight r = p.fiberMean F r w := by
  unfold fiberLaw fiberMean mean reweight
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : F x = r <;> simp [hx]

theorem fiberLaw_mass_preimage {X R : Type*} [Fintype X] [Fintype R]
    (p : FiniteProbabilityWeights X) (F : X → R) (G : Finset R) :
    (p.fiberLaw F).mass G = p.mass (Finset.univ.filter (fun x => F x ∈ G)) := by
  unfold mass fiberLaw fiberMean mean
  simp only [Finset.sum_filter, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [eq_comm]

theorem reweight_lowWeightFibers_mass {X R : Type*} [Fintype X] [Fintype R]
    (p : FiniteProbabilityWeights X) (F : X → R) (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hmean : p.mean w = 1) {η : ℝ} (hη : 0 ≤ η) :
    (p.reweight w hw hmean).mass
      (Finset.univ.filter (fun x => F x ∈ p.lowWeightFibers F w η)) ≤ η := by
  rw [← fiberLaw_mass_preimage]
  unfold mass
  simp only [reweight_fiberLaw_weight]
  exact p.lowWeightFibers_weighted_mass F w hη

theorem norm_complexMean_remove_set_le_mass {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (G : Finset X) (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖p.complexMean f - p.complexMean (fun x => if x ∈ G then 0 else f x)‖ ≤ p.mass G := by
  rw [← p.mean_indicator G]
  apply p.norm_complexMean_sub_le
  intro x _
  by_cases hx : x ∈ G
  · simpa only [hx, ite_true, sub_zero] using hf x
  · simp only [hx, ite_false, sub_self, norm_zero, le_refl]

theorem reweight_remove_lowWeightFibers_error {X R : Type*} [Fintype X] [Fintype R]
    (p : FiniteProbabilityWeights X) (F : X → R) (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hmean : p.mean w = 1) {η : ℝ} (hη : 0 ≤ η)
    (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖(p.reweight w hw hmean).complexMean f -
      (p.reweight w hw hmean).complexMean
        (fun x => if x ∈ Finset.univ.filter (fun y => F y ∈ p.lowWeightFibers F w η) then 0 else f x)‖ ≤ η :=
  ((p.reweight w hw hmean).norm_complexMean_remove_set_le_mass _ f hf).trans
    (p.reweight_lowWeightFibers_mass F w hw hmean hη)

end Erdos3.FiniteProbabilityWeights

end

end OAI
