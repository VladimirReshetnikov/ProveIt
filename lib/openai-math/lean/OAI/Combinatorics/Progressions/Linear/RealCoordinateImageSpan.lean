import OAI.Combinatorics.Progressions.Geometry.RealCoordinateFunctionals

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {V J B : Type*} [AddCommGroup V] [Module ℚ V]

theorem coordinateImage_eq_span (U : Submodule ℚ V) (g : J → V)
    (hg : Submodule.span ℚ (Set.range g) = U) (ℓ : V →ₗ[ℚ] (B → ℚ)) :
    U.map ℓ = Submodule.span ℚ (Set.range (fun j => ℓ (g j))) := by
  rw [← hg, Submodule.map_span, ← Set.range_comp]
  rfl

theorem realifyCoordinateMap_image_eq_span (U : Submodule ℚ V) (g : J → V)
    (hg : Submodule.span ℚ (Set.range g) = U) (ℓ : V →ₗ[ℚ] (B → ℚ)) :
    (U.baseChange ℝ).map (realifyCoordinateMap ℓ) =
      Submodule.span ℝ (Set.range (fun j i => (ℓ (g j) i : ℝ))) := by
  rw [← hg, Submodule.baseChange_span, Submodule.map_span, Set.image_image, ← Set.range_comp]
  apply congrArg (Submodule.span ℝ)
  apply congrArg Set.range
  funext j i
  exact (realifyCoordinateMap_tmul ℓ 1 (g j) i).trans (one_mul _)

theorem realifyCoordinateMap_mem_span (U : Submodule ℚ V) (g : J → V)
    (hg : Submodule.span ℚ (Set.range g) = U) (ℓ : V →ₗ[ℚ] (B → ℚ))
    {x : ℝ ⊗[ℚ] V} (hx : x ∈ U.baseChange ℝ) :
    realifyCoordinateMap ℓ x ∈
      Submodule.span ℝ (Set.range (fun j i => (ℓ (g j) i : ℝ))) := by
  rw [← realifyCoordinateMap_image_eq_span U g hg ℓ]
  exact ⟨x, hx, rfl⟩

theorem mem_coordinateColumn_span_iff (U : Submodule ℚ V) (g : J → V)
    (hg : Submodule.span ℚ (Set.range g) = U) (ℓ : V →ₗ[ℚ] (B → ℚ)) (y : B → ℝ) :
    y ∈ Submodule.span ℝ (Set.range (fun j i => (ℓ (g j) i : ℝ))) ↔
      ∃ x ∈ U.baseChange ℝ, realifyCoordinateMap ℓ x = y := by
  rw [← realifyCoordinateMap_image_eq_span U g hg ℓ]
  rfl

end Erdos3

end

end OAI
