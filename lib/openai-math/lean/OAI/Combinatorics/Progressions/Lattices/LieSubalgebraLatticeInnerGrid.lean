import OAI.Combinatorics.Progressions.Estimates.PetalComparisonTree

namespace OAI

section

namespace Erdos3

open Module
open scoped BigOperators Matrix TensorProduct

theorem integralVector_mulVec_of_column_denominators
    {ι κ : Type*} [Fintype κ] (B : Matrix ι κ ℚ) (q : ℕ)
    (hB : ∀ j, B.col j ∈ denominatorGrid q) (z : κ → ℤ) :
    IntegralVector (B *ᵥ ((q : ℚ) • (fun j => (z j : ℚ)))) := by
  classical
  choose c hc using hB
  refine ⟨fun i => ∑ j, c j i * z j, fun i => ?_⟩
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Int.cast_sum,
    Int.cast_mul]
  apply Finset.sum_congr rfl
  intro j _
  have h : (q : ℚ) * B i j = (c j i : ℚ) := hc j i
  rw [← h]
  ring

theorem scaledIntegerGrid_mulVec_of_column_denominators
    {ι κ : Type*} [Fintype κ] (B : Matrix ι κ ℚ) (l q : ℕ)
    (hB : ∀ j, B.col j ∈ denominatorGrid q) :
    scaledIntegerGrid (l * q) ⊆ B.mulVec ⁻¹' scaledIntegerGrid l := by
  rintro x ⟨z, rfl⟩
  have h := scaled_grid_mulVec B l _ (integralVector_mulVec_of_column_denominators B q hB z)
  simpa only [Set.mem_preimage, smul_smul, Nat.cast_mul] using h

theorem bchSubgroup_comap_inner_grid_of_columns
    {ι κ L M : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}
    (b : Basis κ ℚ M) (e : Basis ι ℚ L) (φ : M →ₗ⁅ℚ⁆ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hL)) (l q : ℕ)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (hcolumns : ∀ j, e.equivFun (φ (b j)) ∈ denominatorGrid q) :
    scaledIntegerGrid (l * q) ⊆ bchSubgroupCoordinates b
      (Γ.comap (NilpotentLieBCHGroup.map (hnil := hM) φ)) := by
  rw [bchSubgroupCoordinates_comap b e φ Γ]
  have hB : ∀ j, (LinearMap.toMatrix b e φ.toLinearMap).col j ∈ denominatorGrid q := by
    intro j
    have he : (LinearMap.toMatrix b e φ.toLinearMap).col j =
        e.equivFun (φ (b j)) := by
      funext i
      exact LinearMap.toMatrix_apply b e φ.toLinearMap i j
    rw [he]
    exact hcolumns j
  intro x hx
  exact hinner (scaledIntegerGrid_mulVec_of_column_denominators _ l q hB hx)

theorem lieSubalgebra_comap_inner_grid_of_columns
    {ι κ L : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    (K : LieSubalgebra ℚ L) (bk : Basis κ ℚ K) (b : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l q : ℕ)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates b Γ)
    (hcolumns : ∀ j, b.equivFun (bk j : L) ∈ denominatorGrid q) :
    scaledIntegerGrid (l * q) ⊆ bchSubgroupCoordinates bk
      (Γ.comap (NilpotentLieBCHGroup.map
        (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K) K.incl)) :=
  bchSubgroup_comap_inner_grid_of_columns bk b K.incl Γ l q hinner hcolumns

namespace NilpotentLieBCHGroup

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]
variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem realification_comap_incl_mem (K : LieSubalgebra ℚ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (x : NilpotentLieBCHGroup (ℝ ⊗[ℚ] K) s
      (realification_lowerCentralSeries_eq_bot (lie_subalgebra_lowerCentralSeries_eq_bot hnil K)))
    (hx : x ∈ (Γ.comap
      (map (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K) K.incl)).map
      (realificationHom (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K))) :
    realificationMap (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K)
      (hM := hnil) K.incl x ∈ Γ.map realificationHom := by
  change x ∈ (Γ.map realificationHom).comap
    (realificationMap (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K)
      (hM := hnil) K.incl)
  rw [realification_subgroup_comap_incl]
  exact hx

theorem realification_comap_incl_map_le (K : LieSubalgebra ℚ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) :
    ((Γ.comap (map (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K) K.incl)).map
      (realificationHom (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K))).map
      (realificationMap (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K)
        (hM := hnil) K.incl) ≤ Γ.map realificationHom := by
  rw [← realification_subgroup_comap_incl]
  exact Subgroup.map_comap_le _ _

end NilpotentLieBCHGroup

end Erdos3

end

end OAI
