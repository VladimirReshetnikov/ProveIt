import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open scoped NNReal ContDiff

theorem exists_smoothTransition_lipschitz :
    ∃ A : ℝ≥0, 1 ≤ A ∧ LipschitzWith A Real.smoothTransition := by
  have hs : ContDiffOn ℝ 1 Real.smoothTransition (Set.Icc (0 : ℝ) 1) :=
    Real.smoothTransition.contDiff.contDiffOn
  obtain ⟨K, hK⟩ := hs.exists_lipschitzOnWith one_ne_zero (convex_Icc _ _) isCompact_Icc
  have hglobal : LipschitzWith K Real.smoothTransition := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hx := (Set.projIcc (0 : ℝ) 1 zero_le_one x).property
    have hy := (Set.projIcc (0 : ℝ) 1 zero_le_one y).property
    have h := hK.dist_le_mul _ hx _ hy
    simp only [Real.smoothTransition.projIcc] at h
    have hp := (LipschitzWith.projIcc (a := (0 : ℝ)) (b := 1) zero_le_one).dist_le_mul x y
    simp only [NNReal.coe_one, one_mul] at hp
    exact h.trans (mul_le_mul_of_nonneg_left hp K.coe_nonneg)
  exact ⟨K + 1, by simp, hglobal.weaken (by simp)⟩

noncomputable def halfspaceCutoff {E : Type*} (r : ℝ) (d : E → ℝ) (x : E) : ℝ :=
  Real.smoothTransition (d x / r - 1)

theorem halfspaceCutoff_range {E : Type*} (r : ℝ) (d : E → ℝ) (x : E) :
    halfspaceCutoff r d x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem halfspaceCutoff_eq_zero {E : Type*} {r : ℝ} (hr : 0 < r)
    (d : E → ℝ) {x : E} (hx : d x ≤ r) : halfspaceCutoff r d x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact sub_nonpos.mpr ((div_le_one hr).mpr hx)

theorem halfspaceCutoff_eq_one {E : Type*} {r : ℝ} (hr : 0 < r)
    (d : E → ℝ) {x : E} (hx : 2 * r ≤ d x) : halfspaceCutoff r d x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have h := (le_div_iff₀ hr).mpr hx
  linarith

theorem halfspaceCutoff_tsupport_subset {E : Type*} [TopologicalSpace E]
    {r : ℝ} (hr : 0 < r) (d : E → ℝ) (hd : Continuous d) :
    tsupport (halfspaceCutoff r d) ⊆ {x | r ≤ d x} := by
  apply closure_minimal _ (isClosed_le continuous_const hd)
  intro x hx
  change r ≤ d x
  by_contra! h
  exact hx (halfspaceCutoff_eq_zero hr d h.le)

theorem contDiff_halfspaceCutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (d : E → ℝ) (hd : ContDiff ℝ ∞ d) : ContDiff ℝ ∞ (halfspaceCutoff r d) :=
  Real.smoothTransition.contDiff.comp ((hd.div_const r).sub contDiff_const)

theorem halfspaceCutoff_fderiv_norm_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℝ≥0) (hLip : LipschitzWith A Real.smoothTransition)
    {r : ℝ} (hr : 0 < r) (d : E → ℝ) {x : E} (hd : DifferentiableAt ℝ d x) :
    ‖fderiv ℝ (halfspaceCutoff r d) x‖ ≤ (A : ℝ) / r * ‖fderiv ℝ d x‖ := by
  have ht : DifferentiableAt ℝ Real.smoothTransition (r⁻¹ • d x - 1) :=
    ((Real.smoothTransition.contDiff : ContDiff ℝ 1 _).differentiable one_ne_zero).differentiableAt
  have heq : halfspaceCutoff r d = Real.smoothTransition ∘ (fun y => r⁻¹ • d y - 1) := by
    funext y
    simp only [halfspaceCutoff, Function.comp_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [heq]
  change ‖fderiv ℝ (Real.smoothTransition ∘ (fun y => (r⁻¹ • d) y - 1)) x‖ ≤ _
  rw [fderiv_comp x ht ((hd.const_smul r⁻¹).sub_const 1),
    fderiv_sub_const, fderiv_const_smul hd]
  calc
    _ ≤ ‖fderiv ℝ Real.smoothTransition (r⁻¹ • d x - 1)‖ * ‖r⁻¹ • fderiv ℝ d x‖ :=
      (fderiv ℝ Real.smoothTransition _).opNorm_comp_le _
    _ ≤ (A : ℝ) * ‖r⁻¹ • fderiv ℝ d x‖ :=
      mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hLip) (norm_nonneg _)
    _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]; ring

end Erdos3

end

end OAI
