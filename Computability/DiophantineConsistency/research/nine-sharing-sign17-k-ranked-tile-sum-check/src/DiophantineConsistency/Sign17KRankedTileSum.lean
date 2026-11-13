import DiophantineConsistency.Sign17KGlobalAssembly

/-! SOURCE-ONLY: reindex the actual tile term sum by the checked candidate. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KRankedTileSum
open WangTiles942 MF.WangTiles942
open scoped BigOperators

theorem candidate_injective : Function.Injective Sign17KWeightUnion942.indices := by
  intro i j h
  have hpos := congrArg physicalMap h
  simpa only [Sign17KGlobalAssembly.candidate_positions] using hpos

theorem candidate_bijective : Function.Bijective Sign17KWeightUnion942.indices :=
  ⟨candidate_injective, Finite.surjective_of_injective _ candidate_injective⟩

theorem physical_position (i : Fin 942) :
    physicalPosition (Sign17KWeightUnion942.indices i) = i.val := by
  have h := congrArg Fin.val (Sign17KGlobalAssembly.candidate_positions i)
  exact h

theorem ranked_tile_sum (r : ℕ) :
    (∑ i : Fin 942, 2 * selectorWeight (tile i) * r ^ (1005 - physicalPosition i)) =
      ∑ i : Fin 942, 2 * Sign17KWeightUnion942.weights i * r ^ (1005 - i.val) := by
  calc
    (∑ i : Fin 942, 2 * selectorWeight (tile i) * r ^ (1005 - physicalPosition i)) =
        ∑ i : Fin 942, 2 * selectorWeight (tile (Sign17KWeightUnion942.indices i)) *
          r ^ (1005 - physicalPosition (Sign17KWeightUnion942.indices i)) := by
      exact (candidate_bijective.sum_comp
        (fun i => 2 * selectorWeight (tile i) * r ^ (1005 - physicalPosition i))).symm
    _ = ∑ i : Fin 942, 2 * Sign17KWeightUnion942.weights i * r ^ (1005 - i.val) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Sign17KWeightUnion942.all_weights, physical_position]

end DiophantineConsistency.Sign17KRankedTileSum
#print axioms DiophantineConsistency.Sign17KRankedTileSum.candidate_bijective
#print axioms DiophantineConsistency.Sign17KRankedTileSum.physical_position
#print axioms DiophantineConsistency.Sign17KRankedTileSum.ranked_tile_sum
