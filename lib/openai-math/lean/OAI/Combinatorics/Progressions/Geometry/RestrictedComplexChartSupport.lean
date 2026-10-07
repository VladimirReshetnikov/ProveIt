import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import OAI.Combinatorics.Progressions.Probability.RestrictedComplexChartDensityComparison

namespace OAI

section

namespace Erdos3

variable {X Y : Type*}

theorem restrictedComplexChartDensity_norm_le (q : X → Y) (S : Set X)
    (hinj : Set.InjOn q S) (f : X → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ x, ‖f x‖ ≤ C) (y : Y) : ‖restrictedComplexChartDensity q S 1 f y‖ ≤ C := by
  by_cases hy : y ∈ q '' S
  · obtain ⟨x, hx, rfl⟩ := hy
    rw [restrictedComplexChartDensity_apply q S 1 f hinj hx, Complex.ofReal_one, one_mul]
    exact hf x
  · rw [restrictedComplexChartDensity_zero q S 1 f hy, norm_zero]
    exact hC

theorem restrictedComplexChartDensity_enlarge (q : X → Y) (S T : Set X)
    (hST : S ⊆ T) (hinj : Set.InjOn q T) (c : ℝ) (f : X → ℂ)
    (hsupport : Function.support f ⊆ S) :
    restrictedComplexChartDensity q S c f = restrictedComplexChartDensity q T c f := by
  funext y
  by_cases hy : y ∈ q '' T
  · obtain ⟨x, hx, rfl⟩ := hy
    rw [restrictedComplexChartDensity_apply q T c f hinj hx]
    by_cases hxs : x ∈ S
    · exact restrictedComplexChartDensity_apply q S c f (hinj.mono hST) hxs
    · have hzero : f x = 0 := by
        by_contra hf
        exact hxs (hsupport hf)
      have hout : q x ∉ q '' S := by
        rintro ⟨z, hz, he⟩
        exact hxs ((hinj (hST hz) hx he) ▸ hz)
      rw [restrictedComplexChartDensity_zero q S c f hout, hzero, mul_zero]
  · have hs : y ∉ q '' S := fun h => hy (Set.image_mono hST h)
    rw [restrictedComplexChartDensity_zero q S c f hs,
      restrictedComplexChartDensity_zero q T c f hy]

theorem restrictedComplexChartDensity_measurable [MeasurableSpace X] [MeasurableSpace Y]
    (q : X → Y) (S : Set X) (he : MeasurableEmbedding (fun x : S => q x.val))
    (c : ℝ) (f : X → ℂ) (hf : Measurable f) :
    Measurable (restrictedComplexChartDensity q S c f) :=
  measurable_const.mul (he.measurable_extend (hf.comp measurable_subtype_coe) measurable_const)

end Erdos3

end

end OAI
