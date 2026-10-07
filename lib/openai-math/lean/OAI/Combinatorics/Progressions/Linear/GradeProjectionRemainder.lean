/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.CurrentLayerSplitting
import OAI.Combinatorics.Progressions.Estimates.SymbolAbsorptionBounds

namespace OAI

section

namespace Erdos3

open Module

section Coordinates

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem basisGradeProjection_eq_zero_of_mem_higher (b : Basis ι K V)
    (w : ι → ℕ) (k : ℕ) (x : V)
    (hx : x ∈ Submodule.span K (b '' {i | k + 1 ≤ w i})) :
    basisGradeProjection b w k x = 0 := by
  apply (basisCoordinateProjection_eq_zero_iff b {i | w i = k} x).mpr
  apply Submodule.span_mono (Set.image_mono ?_) hx
  intro i hi
  change w i ≠ k
  change k + 1 ≤ w i at hi
  omega

theorem sub_basisGradeProjection_mem_higher (b : Basis ι K V)
    (w : ι → ℕ) (k : ℕ) (x : V)
    (hx : x ∈ Submodule.span K (b '' {i | k ≤ w i})) :
    x - basisGradeProjection b w k x ∈ Submodule.span K (b '' {i | k + 1 ≤ w i}) := by
  apply (basis_mem_span_image_iff b _ _).mpr
  intro i hi
  change ¬ k + 1 ≤ w i at hi
  rw [map_sub, Finsupp.sub_apply, basisGradeProjection_repr]
  by_cases hki : w i = k
  · simp only [hki, ↓reduceIte, sub_self]
  · rw [ite_eq_right hki, sub_zero]
    exact (basis_mem_span_image_iff b _ x).mp hx i (by
      change ¬ k ≤ w i
      omega)

theorem BasisGradedSubmodule.mem_sup_higher_of_grade (b : Basis ι K V)
    (w : ι → ℕ) (U : Submodule K V) (hU : BasisGradedSubmodule b w U)
    (k : ℕ) (x : V) (hx : x ∈ U ⊔ Submodule.span K (b '' {i | k ≤ w i}))
    (hgrade : basisGradeProjection b w k x ∈ U) :
    x ∈ U ⊔ Submodule.span K (b '' {i | k + 1 ≤ w i}) := by
  obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  have hgz : basisGradeProjection b w k z ∈ U := by
    have h := U.sub_mem hgrade (hU k u hu)
    simpa only [map_add, add_sub_cancel_left] using h
  refine Submodule.mem_sup.mpr ⟨u + basisGradeProjection b w k z, U.add_mem hu hgz,
    z - basisGradeProjection b w k z, sub_basisGradeProjection_mem_higher b w k z hz, ?_⟩
  abel

end Coordinates

namespace NilpotentLieFiltration

open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

include hlayers in
theorem realGradeProjection_eq_zero_of_mem_next_layer (k : ℕ) (x : ℝ ⊗[ℚ] L)
    (hx : x ∈ F.realification.layer (k + 1)) :
    basisGradeProjection (b.baseChange ℝ) w k x = 0 := by
  apply basisGradeProjection_eq_zero_of_mem_higher
  change x ∈ (F.realLayer (k + 1)).toSubmodule at hx
  rwa [F.realLayer_eq_span_basis b (k + 1) _ (hlayers (k + 1))] at hx

include hlayers in
theorem realGradeProjection_bch_triple (k : ℕ) (a p d : ℝ ⊗[ℚ] L)
    (ha : a ∈ F.realification.layer k) (hd : d ∈ F.realification.layer k) :
    basisGradeProjection (b.baseChange ℝ) w k (lieBCH s (lieBCH s a p) d) =
      basisGradeProjection (b.baseChange ℝ) w k a +
        basisGradeProjection (b.baseChange ℝ) w k p +
        basisGradeProjection (b.baseChange ℝ) w k d := by
  have h := F.realGradeProjection_eq_zero_of_mem_next_layer b w hlayers k _
    (F.realification.bch_triple_sub_sum_mem_next_layer k a p d ha hd)
  simpa only [map_sub, map_add, sub_eq_zero] using h

include hlayers in
theorem realGradeProjection_normalized_splitting (k : ℕ)
    (E P R E₀ R₀ : F.realification.Group)
    (hE : NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) E₀ =
      NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) E)
    (hR : NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) R =
      NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) R₀) :
    basisGradeProjection (b.baseChange ℝ) w k (E₀⁻¹ * (E * P * R) * R₀⁻¹).coord =
      basisGradeProjection (b.baseChange ℝ) w k (E₀⁻¹ * E).coord +
        basisGradeProjection (b.baseChange ℝ) w k P.coord +
        basisGradeProjection (b.baseChange ℝ) w k (R * R₀⁻¹).coord := by
  have h := F.realGradeProjection_eq_zero_of_mem_next_layer b w hlayers k _
    (F.realification.normalized_splitting_sub_sum_mem_next_layer k E P R E₀ R₀ hE hR)
  simpa only [map_sub, map_add, sub_eq_zero] using h

include hlayers in

theorem realGradeProjection_normalized_residual_mem
    (U : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hU : BasisGradedSubmodule (b.baseChange ℝ) w U) (k : ℕ)
    (E P R E₀ R₀ : F.realification.Group) (hP : P.coord ∈ U)
    (hE : NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) E₀ =
      NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) E)
    (hR : NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) R =
      NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) R₀) :
    basisGradeProjection (b.baseChange ℝ) w k (E₀⁻¹ * (E * P * R) * R₀⁻¹).coord -
      basisGradeProjection (b.baseChange ℝ) w k (E₀⁻¹ * E).coord -
      basisGradeProjection (b.baseChange ℝ) w k (R * R₀⁻¹).coord ∈ U := by
  rw [F.realGradeProjection_normalized_splitting b w hlayers k E P R E₀ R₀ hE hR]
  convert hU k P.coord hP using 1
  abel

end NilpotentLieFiltration
end Erdos3

end

end OAI
