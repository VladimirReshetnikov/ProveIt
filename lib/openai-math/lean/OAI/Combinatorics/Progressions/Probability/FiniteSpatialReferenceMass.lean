import OAI.Combinatorics.Progressions.Estimates.FiniteFiberTest

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem norm_spatial_reference_sum_sub {T : Type*} [Fintype T]
    (weight profile : T → ℝ) (a b test : T → ℂ)
    {A E : ℝ} (hA : 0 < A) (hE : 0 ≤ E) (hw : ∀ t, 0 ≤ weight t)
    (htest : ∀ t, ‖test t‖ ≤ 1) (hab : ∀ t, ‖a t - b t‖ ≤ E) :
    ‖(∑ t, (weight t : ℂ) * (a t / (A : ℂ)) * test t * (profile t : ℂ)) -
      (∑ t, (weight t : ℂ) * (b t / (A : ℂ)) * test t * (profile t : ℂ))‖ ≤
      E * ∑ t, weight t * |profile t| / A := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro t _
  have hid : (weight t : ℂ) * (a t / (A : ℂ)) * test t * (profile t : ℂ) -
      (weight t : ℂ) * (b t / (A : ℂ)) * test t * (profile t : ℂ) =
        (weight t : ℂ) * ((a t - b t) / (A : ℂ)) * test t * (profile t : ℂ) := by ring
  rw [hid, norm_mul, norm_mul, norm_mul, norm_div, Complex.norm_real,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (hw t), abs_of_pos hA]
  calc
    _ ≤ weight t * (E / A) * 1 * |profile t| := by
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hab t) hA.le) (hw t))
        (htest t) (norm_nonneg _) (mul_nonneg (hw t) (div_nonneg hE hA.le))
    _ = _ := by ring

theorem norm_nested_spatial_reference_sub {Ω R T : Type*}
    [Fintype Ω] [Fintype R] [Fintype T]
    (p : FiniteProbabilityWeights Ω) (q : FiniteProbabilityWeights R)
    (weight : T → ℝ) (profile : Ω → R → T → ℝ) (a b test : Ω → R → T → ℂ)
    {A E Z : ℝ} (hA : 0 < A) (hE : 0 ≤ E) (hZ : 0 < Z)
    (hw : ∀ t, 0 ≤ weight t) (htest : ∀ u r t, ‖test u r t‖ ≤ 1)
    (hab : ∀ u r t, ‖a u r t - b u r t‖ ≤ E) :
    ‖p.complexMean (fun u => q.complexMean (fun r =>
        ∑ t, (weight t : ℂ) * (a u r t / (A : ℂ)) * test u r t * (profile u r t : ℂ))) / (Z : ℂ) -
      p.complexMean (fun u => q.complexMean (fun r =>
        ∑ t, (weight t : ℂ) * (b u r t / (A : ℂ)) * test u r t * (profile u r t : ℂ))) / (Z : ℂ)‖ ≤
      E * (p.mean (fun u => q.mean (fun r => ∑ t, weight t * |profile u r t| / A)) / Z) := by
  have hi (u : Ω) :
      ‖q.complexMean (fun r => ∑ t,
          (weight t : ℂ) * (a u r t / (A : ℂ)) * test u r t * (profile u r t : ℂ)) -
        q.complexMean (fun r => ∑ t,
          (weight t : ℂ) * (b u r t / (A : ℂ)) * test u r t * (profile u r t : ℂ))‖ ≤
        E * q.mean (fun r => ∑ t, weight t * |profile u r t| / A) := by
    apply (q.norm_complexMean_sub_le _ _
      (fun r => E * ∑ t, weight t * |profile u r t| / A) ?_).trans_eq
      (q.mean_const_mul E _)
    intro r _
    exact norm_spatial_reference_sum_sub weight (profile u r) (a u r) (b u r) (test u r)
      hA hE hw (htest u r) (hab u r)
  have ho := (p.norm_complexMean_sub_le _ _
    (fun u => E * q.mean (fun r => ∑ t, weight t * |profile u r t| / A))
    (fun u _ => hi u)).trans_eq (p.mean_const_mul E _)
  rw [← sub_div, norm_div, Complex.norm_real, Real.norm_of_nonneg hZ.le]
  exact (div_le_div_of_nonneg_right ho hZ.le).trans_eq (by ring)

end Erdos3

end

end OAI
