import DiophantineConsistency.Sign17KRankGeneric
import DiophantineConsistency.MFWangTiles942Permutation

/-! SOURCE-ONLY: conditional specialization to the actual physical map. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KActualRank
open MF.WangTiles942 WangTiles942

theorem candidate_positions (f : Fin 942 → Fin 942)
    (hzero : f 0 = 0)
    (hnonzero : ∀ i, i ≠ 0 → f i ≠ 0)
    (hdesc : ∀ i j, i < j → i ≠ 0 →
      selectorWeight (tile (f j)) < selectorWeight (tile (f i))) :
    ∀ i, physicalMap (f i) = i := by
  apply Sign17KRankGeneric.candidate_positions physicalMap f
    (fun i => selectorWeight (tile i)) physicalMap_zero physicalMap_injective
  · intro a b ha hb
    change physicalPosition a < physicalPosition b ↔ _
    exact physical_lt_iff_weight a b ha hb
  · exact hzero
  · exact hnonzero
  · exact hdesc

end DiophantineConsistency.Sign17KActualRank
#print axioms DiophantineConsistency.Sign17KActualRank.candidate_positions
