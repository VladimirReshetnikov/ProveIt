import OAI.Combinatorics.Progressions.Estimates.PetalComparisonTree

namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open scoped TensorProduct

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}
    (φ : L →ₗ⁅ℚ⁆ M) (U : LieSubalgebra ℚ L)

theorem realificationSubgroup_map :
    (realificationSubgroup (hnil := hL) U).map
      (realificationMap (hnil := hL) (hM := hM) φ) =
        realificationSubgroup (hnil := hM) (U.map φ) := by
  ext g
  change (∃ x, x.coord ∈ realificationLieSubalgebra U ∧
    realificationMap (hnil := hL) (hM := hM) φ x = g) ↔
      g.coord ∈ realificationLieSubalgebra (U.map φ)
  have hreal : (U.map φ).toSubmodule.baseChange ℝ =
      (U.toSubmodule.baseChange ℝ).map (φ.toLinearMap.baseChange ℝ) :=
    realification_map U.toSubmodule φ.toLinearMap
  change _ ↔ g.coord ∈ (U.map φ).toSubmodule.baseChange ℝ
  rw [hreal]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.coord, hx, rfl⟩
  · rintro ⟨x, hx, hφx⟩
    exact ⟨⟨x⟩, hx, ext hφx⟩

theorem exists_real_prescribed_image_factors
    (E P R : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s
      (realification_lowerCentralSeries_eq_bot hL))
    (EF RF : NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) t
      (realification_lowerCentralSeries_eq_bot hM))
    (hP : P ∈ realificationSubgroup (hnil := hL) U)
    (hleft : ((realificationMap (hnil := hL) (hM := hM) φ E)⁻¹ * EF) ∈
      realificationSubgroup (hnil := hM) (U.map φ))
    (hright : (RF * (realificationMap (hnil := hL) (hM := hM) φ R)⁻¹) ∈
      realificationSubgroup (hnil := hM) (U.map φ)) :
    ∃ A D : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s
      (realification_lowerCentralSeries_eq_bot hL),
      A ∈ realificationSubgroup (hnil := hL) U ∧
      D ∈ realificationSubgroup (hnil := hL) U ∧
      (E * A) * (A⁻¹ * P * D⁻¹) * (D * R) = E * P * R ∧
      A⁻¹ * P * D⁻¹ ∈ realificationSubgroup (hnil := hL) U ∧
      realificationMap (hnil := hL) (hM := hM) φ (E * A) = EF ∧
      realificationMap (hnil := hL) (hM := hM) φ (D * R) = RF := by
  rw [← realificationSubgroup_map (hL := hL) (hM := hM) φ U] at hleft hright
  obtain ⟨A, hA, hAE⟩ := hleft
  obtain ⟨D, hD, hDR⟩ := hright
  refine ⟨A, D, hA, hD, by group, ?_, ?_, ?_⟩
  · exact (realificationSubgroup U).mul_mem
      ((realificationSubgroup U).mul_mem ((realificationSubgroup U).inv_mem hA) hP)
      ((realificationSubgroup U).inv_mem hD)
  · rw [map_mul, hAE, mul_inv_cancel_left]
  · rw [map_mul, hDR, inv_mul_cancel_right]

end Erdos3.NilpotentLieBCHGroup

end

end OAI
