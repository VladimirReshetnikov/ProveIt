import OAI.Combinatorics.Progressions.Lattices.RealifiedSubgroupLattice
import OAI.Combinatorics.Progressions.Nilpotent.ChosenBCHGrids

namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem realificationSubgroup_closed (e : Basis ι ℚ L) (K : LieSubalgebra ℚ L) :
    IsClosed (realificationSubgroup (hnil := hnil) K : Set
      (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil))) := by
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L) := (e.baseChange ℝ).finiteDimensional_of_finite
  exact realLieSubgroup_closed (realificationLieSubalgebra K)

omit [Fintype ι] [T2Space (ℝ ⊗[ℚ] L)] in
theorem realificationSubgroup_connected_simplyConnected (K : LieSubalgebra ℚ L) :
    ConnectedSpace (realificationSubgroup (hnil := hnil) K) ∧
      SimplyConnectedSpace (realificationSubgroup (hnil := hnil) K) :=
  realLieSubgroup_connected_simplyConnected (realificationLieSubalgebra K)

theorem realificationSubgroup_lattice_closed_discrete (e : Basis ι ℚ L) (K : LieSubalgebra ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) :
    let Λ := (Γ.map realificationHom).comap (realificationSubgroup (hnil := hnil) K).subtype
    IsClosed (Λ : Set (realificationSubgroup (hnil := hnil) K)) ∧
      IsDiscrete (Λ : Set (realificationSubgroup (hnil := hnil) K)) := by
  have hΓ := realification_subgroup_closed_discrete e Γ l hl houter
  exact ⟨hΓ.1.preimage continuous_subtype_val,
    hΓ.2.preimage continuous_subtype_val.continuousOn Subtype.val_injective⟩

omit [T2Space (ℝ ⊗[ℚ] L)] in
theorem realificationSubgroup_lattice_cocompact (e : Basis ι ℚ L) (K : LieSubalgebra ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) :
    CompactSpace (realificationSubgroup (hnil := hnil) K ⧸
      (Γ.map realificationHom).comap (realificationSubgroup (hnil := hnil) K).subtype) := by
  let : FiniteDimensional ℚ L := e.finiteDimensional_of_finite
  let b := Module.finBasis ℚ K
  obtain ⟨N, hN, hin, hout⟩ := exists_bchSubgroup_comap_grid
    (hM := lie_subalgebra_lowerCentralSeries_eq_bot hnil K) b e K.incl
    (fun _ _ h => Subtype.ext h) Γ l hl hinner houter
  exact compactSpace_realificationSubgroup_quotient K b Γ N hN hin hout

end Erdos3.NilpotentLieBCHGroup

end

end OAI
