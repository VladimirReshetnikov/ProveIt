import Mathlib.Algebra.Module.Projective
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

namespace OAI

section

namespace Erdos3

theorem exists_orthogonal_section
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] (π : E →ₗ[ℝ] F) (hπ : Function.Surjective π) :
    ∃ L : F →ₗ[ℝ] E, (∀ y, π (L y) = y) ∧
      ∀ x, L (π x) = x - (LinearMap.ker π).starProjection x := by
  obtain ⟨s, hs⟩ := π.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hπ)
  have hret : ∀ y, π (s y) = y := fun y => LinearMap.congr_fun hs y
  let K := LinearMap.ker π
  let L : F →ₗ[ℝ] E := (LinearMap.id - K.starProjection.toLinearMap).comp s
  have hL (y : F) : L y = s y - K.starProjection (s y) := rfl
  have hzero (x : E) : π (K.starProjection x) = 0 := K.starProjection_apply_mem x
  have hright (y : F) : π (L y) = y := by rw [hL, map_sub, hret, hzero, sub_zero]
  have horth (y : F) : L y ∈ Kᗮ :=
    Submodule.sub_starProjection_mem_orthogonal (s y)
  refine ⟨L, hright, ?_⟩
  intro x
  let w := x - K.starProjection x
  have hw : w ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal x
  have hpw : π w = π x := by change π (x - K.starProjection x) = π x; rw [map_sub, hzero, sub_zero]
  have hk : L (π x) - w ∈ K := by
    change π (L (π x) - w) = 0
    rw [map_sub, hright, hpw, sub_self]
  have ho : L (π x) - w ∈ Kᗮ := Kᗮ.sub_mem (horth _) hw
  have hz : inner ℝ (L (π x) - w) (L (π x) - w) = 0 :=
    Submodule.inner_right_of_mem_orthogonal hk ho
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)

end Erdos3

end

end OAI
