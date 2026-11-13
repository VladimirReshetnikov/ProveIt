import DiophantineConsistency.Sign17KWeightUnion942
import DiophantineConsistency.Sign17KAdjacentRank

/-! SOURCE-ONLY: separate numeric-order transport and conditional actual-rank theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KGlobalRankConditional
open WangTiles942 MF.WangTiles942

theorem actual_adjacent_of_numeric
    (hadj : ∀ i : Fin 940,
      Sign17KWeightUnion942.weights i.succ.succ <
        Sign17KWeightUnion942.weights i.castSucc.succ) :
    ∀ i : Fin 940,
      selectorWeight (tile (Sign17KWeightUnion942.indices i.succ.succ)) <
        selectorWeight (tile (Sign17KWeightUnion942.indices i.castSucc.succ)) := by
  intro i
  rw [Sign17KWeightUnion942.all_weights, Sign17KWeightUnion942.all_weights]
  exact hadj i

theorem candidate_positions_if
    (hzero : Sign17KWeightUnion942.indices 0 = 0)
    (hnonzero : ∀ i, i ≠ 0 → Sign17KWeightUnion942.indices i ≠ 0)
    (hadj : ∀ i : Fin 940,
      Sign17KWeightUnion942.weights i.succ.succ <
        Sign17KWeightUnion942.weights i.castSucc.succ) :
    ∀ i, physicalMap (Sign17KWeightUnion942.indices i) = i := by
  apply Sign17KAdjacentRank.candidate_positions
    Sign17KWeightUnion942.indices hzero hnonzero
  exact actual_adjacent_of_numeric hadj

end DiophantineConsistency.Sign17KGlobalRankConditional
#print axioms DiophantineConsistency.Sign17KGlobalRankConditional.actual_adjacent_of_numeric
#print axioms DiophantineConsistency.Sign17KGlobalRankConditional.candidate_positions_if
