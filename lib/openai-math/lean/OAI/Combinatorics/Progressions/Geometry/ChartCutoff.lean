/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.OpenPartialHomeomorph.Basic

namespace OAI

section

namespace Erdos3

open Set
open scoped NNReal

noncomputable def chartCutoff {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    (e : OpenPartialHomeomorph E X) (ψ : E → ℝ) (x : X) : ℝ := by
  classical
  exact if x ∈ e.target then ψ (e.symm x) else 0

theorem chartCutoff_apply {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    (e : OpenPartialHomeomorph E X) (ψ : E → ℝ) {v : E} (hv : v ∈ e.source) :
    chartCutoff e ψ (e v) = ψ v := by
  simp only [chartCutoff, ite_eq_left (e.map_source hv), e.left_inv hv]

theorem chartCutoff_range {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    (e : OpenPartialHomeomorph E X) (ψ : E → ℝ) (hψ : ∀ v, 0 ≤ ψ v ∧ ψ v ≤ 1) (x : X) :
    0 ≤ chartCutoff e ψ x ∧ chartCutoff e ψ x ≤ 1 := by
  classical
  by_cases hx : x ∈ e.target
  · simpa only [chartCutoff, ite_eq_left hx] using hψ (e.symm x)
  · simp only [chartCutoff, ite_eq_right hx, le_refl, zero_le_one, and_self]

theorem tsupport_chartCutoff_subset {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [T2Space X] (e : OpenPartialHomeomorph E X) (ψ : E → ℝ) {S : Set E}
    (hS : IsCompact S) (hsource : S ⊆ e.source) (hsupport : Function.support ψ ⊆ S) :
    tsupport (chartCutoff e ψ) ⊆ e '' S := by
  classical
  apply closure_minimal ?_ (hS.image_of_continuousOn (e.continuousOn.mono hsource)).isClosed
  intro x hx
  have hxt : x ∈ e.target := by
    by_contra h
    exact hx (by simp only [chartCutoff, ite_eq_right h])
  refine ⟨e.symm x, hsupport ?_, e.right_inv hxt⟩
  simpa only [Function.mem_support, chartCutoff, ite_eq_left hxt] using hx

theorem hasCompactSupport_chartCutoff {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [T2Space X] (e : OpenPartialHomeomorph E X) (ψ : E → ℝ) {S : Set E}
    (hS : IsCompact S) (hsource : S ⊆ e.source) (hsupport : Function.support ψ ⊆ S) :
    HasCompactSupport (chartCutoff e ψ) :=
  (hS.image_of_continuousOn (e.continuousOn.mono hsource)).of_isClosed_subset
    isClosed_closure (tsupport_chartCutoff_subset e ψ hS hsource hsupport)

theorem lipschitz_chartCutoff {E X : Type*} [MetricSpace E] [MetricSpace X]
    (e : OpenPartialHomeomorph E X) (ψ : E → ℝ) (A K δ : ℝ≥0) (hδ : 0 < δ)
    (hψ : ∀ v, 0 ≤ ψ v ∧ ψ v ≤ 1) (hLip : LipschitzWith A ψ)
    (hInv : LipschitzOnWith K e.symm e.target)
    (hgap : ∀ x ∈ e.target, ψ (e.symm x) ≠ 0 → ∀ y ∉ e.target, (δ : ℝ) ≤ dist x y) :
    LipschitzWith (A * K + 1 / δ) (chartCutoff e ψ) := by
  classical
  have hδ' : (0 : ℝ) < δ := hδ
  have hcross (x) (hx : x ∈ e.target) (y) (hy : y ∉ e.target) :
      dist (ψ (e.symm x)) 0 ≤ ((A * K + 1 / δ : ℝ≥0) : ℝ) * dist x y := by
    by_cases hz : ψ (e.symm x) = 0
    · rw [hz, dist_self]
      positivity
    · have hd := hgap x hx hz y hy
      calc
        _ = ψ (e.symm x) := by rw [Real.dist_eq, sub_zero, abs_of_nonneg (hψ _).1]
        _ ≤ 1 := (hψ _).2
        _ ≤ (1 / (δ : ℝ)) * dist x y := by
          have hd' := (div_le_div_iff_of_pos_right hδ').mpr hd
          simpa only [div_self (ne_of_gt hδ'), one_div_mul_eq_div] using hd'
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right ?_ dist_nonneg
          simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_one]
          exact le_add_of_nonneg_left (mul_nonneg A.coe_nonneg K.coe_nonneg)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  by_cases hx : x ∈ e.target <;> by_cases hy : y ∈ e.target
  · simp only [chartCutoff, ite_eq_left hx, ite_eq_left hy]
    calc
      _ ≤ (A : ℝ) * dist (e.symm x) (e.symm y) := hLip.dist_le_mul _ _
      _ ≤ (A : ℝ) * ((K : ℝ) * dist x y) :=
        mul_le_mul_of_nonneg_left (hInv.dist_le_mul x hx y hy) A.coe_nonneg
      _ ≤ _ := by
        simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_one]
        nlinarith [mul_nonneg (one_div_nonneg.mpr δ.coe_nonneg) (dist_nonneg (x := x) (y := y))]
  · simpa only [chartCutoff, ite_eq_left hx, ite_eq_right hy] using hcross x hx y hy
  · simpa only [chartCutoff, ite_eq_right hx, ite_eq_left hy, dist_comm] using hcross y hy x hx
  · simp only [chartCutoff, ite_eq_right hx, ite_eq_right hy, dist_self]
    positivity

end Erdos3

end

end OAI
