import DiophantineConsistency.WangTiles942Permutation

/-!
# Checks of the actual 942-position bijection

These checks use the printed floor rank itself. No sorted weight array,
permutation cache, or assumed injectivity is supplied.
-/

namespace DiophantineConsistency.WangTiles942PermutationChecks

open WangTiles942

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option exponentiation.threshold 1024

example (i j : Fin 942) : tile i = tile j ↔ i = j := tile_injective.eq_iff

example (i j : Fin 942) :
    selectorWeight (tile i) = selectorWeight (tile j) ↔ i = j :=
  tile_weight_injective.eq_iff

example : physicalMap 0 = 0 := physicalMap_zero

example : physicalMap 928 = (504 : Fin 942) := by
  apply Fin.ext
  exact initializer_position

example : physicalEquiv.symm 504 = 928 := by
  apply physicalEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  exact initializer_position.symm

example (p : Fin 942) : ∃! i : Fin 942, physicalMap i = p := by
  obtain ⟨i,hi⟩ := physicalMap_bijective.2 p
  exact ⟨i,hi,fun j hj => physicalMap_bijective.1 (hj.trans hi.symm)⟩

example (i j : Fin 941) (h : i < j) :
    physicalWeight j.succ < physicalWeight i.succ := physicalWeight_strictAnti h

#print axioms recovered_tile
#print axioms tile_injective
#print axioms selectorWeight_injective_on_colors
#print axioms tile_weight_injective
#print axioms floor_weight_indicator
#print axioms strictRank_antitone
#print axioms strictRank_injective
#print axioms physicalPosition_succ
#print axioms physicalPosition_lt
#print axioms physicalPosition_injective
#print axioms physicalMap_bijective
#print axioms physicalEquiv
#print axioms physicalWeight_strictAnti

end DiophantineConsistency.WangTiles942PermutationChecks
