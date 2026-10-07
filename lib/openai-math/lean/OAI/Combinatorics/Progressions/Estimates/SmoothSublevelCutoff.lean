import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open scoped ContDiff NNReal

theorem exists_smooth_scalar_cutoff :
    ∃ A : ℝ≥0, 1 ≤ A ∧ ∃ χ : ℝ → ℝ,
      ContDiff ℝ ∞ χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ x, |x| ≤ 1 / 2 → χ x = 1) ∧
      (∀ x, 3 / 4 ≤ |x| → χ x = 0) ∧ LipschitzWith A χ := by
  let f : ContDiffBump (0 : ℝ) := ⟨1 / 2, 3 / 4, by norm_num, by norm_num⟩
  have hsmooth : ContDiff ℝ 1 f := f.contDiff
  obtain ⟨A, hA⟩ := ContDiff.lipschitzWith_of_hasCompactSupport f.hasCompactSupport hsmooth one_ne_zero
  refine ⟨A + 1, by simp, f, f.contDiff, fun x => ⟨f.nonneg, f.le_one⟩, ?_, ?_, ?_⟩
  · intro x hx
    apply f.one_of_mem_closedBall
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hx
  · intro x hx
    apply f.zero_of_le_dist
    simpa only [Real.dist_eq, sub_zero] using hx
  · exact hA.weaken (by simp)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal ContDiff

theorem exists_smooth_sublevel_cutoff :
    ∃ A : ℝ≥0, 1 ≤ A ∧ ∃ ψ : ℝ → ℝ,
      ContDiff ℝ ∞ ψ ∧ (∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ t, |t| ≤ 1 → ψ t = 0) ∧
      (∀ t, 2 ≤ |t| → ψ t = 1) ∧ LipschitzWith A ψ := by
  obtain ⟨A, hA, χ, hs, hrange, hone, hzero, hLip⟩ := exists_smooth_scalar_cutoff
  refine ⟨A, hA, fun t => 1 - χ (t / 2), ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_const.sub (hs.comp (contDiff_id.div_const 2))
  · intro t
    exact ⟨sub_nonneg.mpr (hrange _).2, by linarith [(hrange (t / 2)).1]⟩
  · intro t ht
    have ht' : |t / 2| ≤ 1 / 2 := by rw [abs_div]; norm_num; linarith
    simp only [hone (t / 2) ht', sub_self]
  · intro t ht
    have ht' : 3 / 4 ≤ |t / 2| := by rw [abs_div]; norm_num; linarith
    simp only [hzero (t / 2) ht', sub_zero]
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := hLip.dist_le_mul (x / 2) (y / 2)
    rw [Real.dist_eq, Real.dist_eq, ← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
    rw [Real.dist_eq, Real.dist_eq]
    have heq : (1 - χ (x / 2)) - (1 - χ (y / 2)) = -(χ (x / 2) - χ (y / 2)) := by ring
    rw [heq, abs_neg]
    exact h.trans (by nlinarith [A.coe_nonneg, abs_nonneg (x - y)])

noncomputable def sublevelCutoff {E : Type*} (ψ : ℝ → ℝ) (r : ℝ) (d : E → ℝ) (x : E) : ℝ :=
  ψ (d x / r)

theorem sublevelCutoff_range {E : Type*} (ψ : ℝ → ℝ)
    (hψ : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1) (r : ℝ) (d : E → ℝ) (x : E) :
    sublevelCutoff ψ r d x ∈ Set.Icc (0 : ℝ) 1 := hψ _

theorem sublevelCutoff_eq_zero {E : Type*} (ψ : ℝ → ℝ)
    (hψ : ∀ t, |t| ≤ 1 → ψ t = 0) {r : ℝ} (hr : 0 < r)
    (d : E → ℝ) {x : E} (hx : |d x| ≤ r) : sublevelCutoff ψ r d x = 0 := by
  apply hψ
  rw [abs_div, abs_of_pos hr]
  exact (div_le_one hr).mpr hx

theorem sublevelCutoff_eq_one {E : Type*} (ψ : ℝ → ℝ)
    (hψ : ∀ t, 2 ≤ |t| → ψ t = 1) {r : ℝ} (hr : 0 < r)
    (d : E → ℝ) {x : E} (hx : 2 * r ≤ |d x|) : sublevelCutoff ψ r d x = 1 := by
  apply hψ
  rw [abs_div, abs_of_pos hr]
  exact (le_div_iff₀ hr).mpr hx

theorem sublevelCutoff_tsupport_subset {E : Type*} [TopologicalSpace E]
    (ψ : ℝ → ℝ) (hψ : ∀ t, |t| ≤ 1 → ψ t = 0) {r : ℝ} (hr : 0 < r)
    (d : E → ℝ) (hd : Continuous d) :
    tsupport (sublevelCutoff ψ r d) ⊆ {x | r ≤ |d x|} := by
  apply closure_minimal _ (isClosed_le continuous_const hd.abs)
  intro x hx
  change r ≤ |d x|
  by_contra! h
  exact hx (sublevelCutoff_eq_zero ψ hψ hr d h.le)

theorem contDiff_sublevelCutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (r : ℝ) (d : E → ℝ)
    (hd : ContDiff ℝ ∞ d) : ContDiff ℝ ∞ (sublevelCutoff ψ r d) :=
  hψ.comp (hd.div_const r)

theorem sublevelCutoff_fderiv_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (A : ℝ≥0) (hLip : LipschitzWith A ψ)
    {r : ℝ} (hr : 0 < r) (d : E → ℝ) {x : E} (hd : DifferentiableAt ℝ d x) :
    ‖fderiv ℝ (sublevelCutoff ψ r d) x‖ ≤ (A : ℝ) / r * ‖fderiv ℝ d x‖ := by
  have hψd : DifferentiableAt ℝ ψ (r⁻¹ • d x) := hψ.differentiable (by norm_num) |>.differentiableAt
  have heq : sublevelCutoff ψ r d = ψ ∘ (fun y => r⁻¹ • d y) := by
    ext y
    simp only [sublevelCutoff, Function.comp_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [heq]
  change ‖fderiv ℝ (ψ ∘ (r⁻¹ • d)) x‖ ≤ _
  rw [fderiv_comp x hψd (hd.const_smul r⁻¹), fderiv_const_smul hd]
  calc
    _ ≤ ‖fderiv ℝ ψ (r⁻¹ • d x)‖ * ‖r⁻¹ • fderiv ℝ d x‖ :=
      (fderiv ℝ ψ (r⁻¹ • d x)).opNorm_comp_le _
    _ ≤ (A : ℝ) * ‖r⁻¹ • fderiv ℝ d x‖ :=
      mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hLip) (norm_nonneg _)
    _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]; ring

end Erdos3

end

end OAI
