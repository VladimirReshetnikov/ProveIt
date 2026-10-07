import OAI.Combinatorics.Progressions.Estimates.ContinuousCosetMap
import OAI.Combinatorics.Progressions.Estimates.PetalComparisonTree

namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def realificationSubgroupHom (K : LieSubalgebra ℚ L) :
    NilpotentLieBCHGroup (ℝ ⊗[ℚ] K) s
      (realification_lowerCentralSeries_eq_bot (lie_subalgebra_lowerCentralSeries_eq_bot hnil K)) →*
      realificationSubgroup (hnil := hnil) K :=
  (realificationMap (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K)
    (hM := hnil) K.incl).codRestrict _ (realificationMap_incl_mem (hnil := hnil) K)

theorem realificationSubgroupHom_injective (K : LieSubalgebra ℚ L) :
    Function.Injective (realificationSubgroupHom (hnil := hnil) K) := by
  intro x y hxy
  exact realificationMap_incl_injective K (congrArg Subtype.val hxy)

theorem realificationSubgroupHom_surjective (K : LieSubalgebra ℚ L) :
    Function.Surjective (realificationSubgroupHom (hnil := hnil) K) := by
  intro g
  have hg : g.1 ∈ (realificationMap
      (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K) (hM := hnil) K.incl).range := by
    rw [realificationMap_incl_range]
    exact g.2
  obtain ⟨x, hx⟩ := hg
  exact ⟨x, Subtype.ext hx⟩

theorem realificationSubgroupHom_lattice_comap (K : LieSubalgebra ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) :
    ((Γ.map realificationHom).comap (realificationSubgroup (hnil := hnil) K).subtype).comap
      (realificationSubgroupHom (hnil := hnil) K) =
      (Γ.comap (map (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K) K.incl)).map
        (realificationHom (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K)) :=
  realification_subgroup_comap_incl K Γ

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

omit [T2Space (ℝ ⊗[ℚ] L)] in
theorem continuous_realificationSubgroupHom (K : LieSubalgebra ℚ L)
    [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)] [FiniteDimensional ℚ K] :
    Continuous (realificationSubgroupHom (hnil := hnil) K) := by
  have hlinear : Continuous (realificationLieHom K.incl) :=
    (realificationLieHom K.incl).toLinearMap.continuous_of_finiteDimensional
  have hgroup : Continuous (realificationMap
      (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K) (hM := hnil) K.incl) :=
    continuous_map_of_continuous (realLieHomToRat (realificationLieHom K.incl)) hlinear
  exact hgroup.subtype_mk _

omit [T2Space (ℝ ⊗[ℚ] L)] in
theorem compactSpace_realificationSubgroup_quotient {κ : Type*} [Fintype κ]
    (K : LieSubalgebra ℚ L) (b : Basis κ ℚ K)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (N : ℕ) (hN : 0 < N)
    (hinner : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b
      (Γ.comap (map (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K) K.incl)))
    (houter : bchSubgroupCoordinates b
      (Γ.comap (map (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K) K.incl)) ⊆ denominatorGrid N) :
    CompactSpace (realificationSubgroup (hnil := hnil) K ⧸
      (Γ.map realificationHom).comap (realificationSubgroup (hnil := hnil) K).subtype) := by
  let ΓK := Γ.comap (map (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K) K.incl)
  obtain ⟨τ, hA, hS, hT, _, _, _, _, _⟩ := exists_realification_topology_of_grid b ΓK N hN houter
  let : TopologicalSpace (ℝ ⊗[ℚ] K) := τ
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] K) := hA
  let : ContinuousSMul ℝ (ℝ ⊗[ℚ] K) := hS
  let : T2Space (ℝ ⊗[ℚ] K) := hT
  let : FiniteDimensional ℚ K := b.finiteDimensional_of_finite
  let Λ := (Γ.map realificationHom).comap (realificationSubgroup (hnil := hnil) K).subtype
  let : CompactSpace (_ ⧸ Λ.comap (realificationSubgroupHom (hnil := hnil) K)) := by
    change CompactSpace (_ ⧸ ((Γ.map realificationHom).comap
      (realificationSubgroup (hnil := hnil) K).subtype).comap (realificationSubgroupHom (hnil := hnil) K))
    rw [realificationSubgroupHom_lattice_comap]
    exact compactSpace_realification_quotient b ΓK N hN hinner
  exact compactSpace_quotient_of_surjective_hom Λ (realificationSubgroupHom K)
    (continuous_realificationSubgroupHom K) (realificationSubgroupHom_surjective K)

end Erdos3.NilpotentLieBCHGroup

end

end OAI
