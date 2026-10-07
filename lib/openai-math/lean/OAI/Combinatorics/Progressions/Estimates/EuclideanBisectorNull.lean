/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Set
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem linear_levelset_measure_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (f : E →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) : μ {x : E | f x = c} = 0 := by
  let S : AffineSubspace ℝ E := (affineSpan ℝ ({c} : Set ℝ)).comap f.toAffineMap
  have hS : (S : Set E) = {x : E | f x = c} := by
    ext x
    simp [S]
  have hproper : S ≠ ⊤ := by
    intro he
    have hall : ∀ x : E, f x = c := by
      intro x
      have hx : x ∈ S := by rw [he]; trivial
      change x ∈ (S : Set E) at hx
      simpa only [hS, Set.mem_ofPred_eq] using hx
    have hc : c = 0 := by simpa using (hall 0).symm
    apply hf
    ext x
    simpa only [hc, LinearMap.zero_apply] using hall x
  rw [← hS]
  exact μ.addHaar_affineSubspace S hproper

theorem euclidean_bisector_measure_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] (a b : E) (hab : a ≠ b) :
    μ {x : E | ‖x - a‖ = ‖x - b‖} = 0 := by
  let f : E →ₗ[ℝ] ℝ := (innerSL ℝ (b - a)).toLinearMap
  have hf : f ≠ 0 := by
    intro he
    have hz : inner ℝ (b - a) (b - a) = 0 := by
      simpa only [f, ContinuousLinearMap.coe_coe, innerSL_apply_apply,
        LinearMap.zero_apply] using LinearMap.congr_fun he (b - a)
    exact hab (sub_eq_zero.mp ((inner_self_eq_zero).mp hz)).symm
  apply measure_mono_null (t := {x : E | f x = (‖b‖ ^ 2 - ‖a‖ ^ 2) / 2})
  · intro x hx
    change inner ℝ (b - a) x = (‖b‖ ^ 2 - ‖a‖ ^ 2) / 2
    rw [inner_sub_left, real_inner_comm x b, real_inner_comm x a]
    have he : ‖x - a‖ ^ 2 = ‖x - b‖ ^ 2 := congrArg (fun t : ℝ => t ^ 2) hx
    rw [norm_sub_sq_real, norm_sub_sq_real] at he
    linarith
  · exact linear_levelset_measure_zero μ f hf _

end Erdos3

end

end OAI
