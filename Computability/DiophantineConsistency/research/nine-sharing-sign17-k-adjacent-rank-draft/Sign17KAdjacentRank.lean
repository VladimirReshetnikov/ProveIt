import DiophantineConsistency.Sign17KActualRank
import Mathlib.Order.Fin.Basic

/-! SOURCE-ONLY: reduce conditional actual rank to adjacent nonzero weights. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KAdjacentRank
open MF.WangTiles942 WangTiles942

theorem candidate_positions (f : Fin 942 → Fin 942)
    (hzero : f 0 = 0)
    (hnonzero : ∀ i, i ≠ 0 → f i ≠ 0)
    (hadj : ∀ i : Fin 940,
      selectorWeight (tile (f i.succ.succ)) <
        selectorWeight (tile (f i.castSucc.succ))) :
    ∀ i, physicalMap (f i) = i := by
  apply Sign17KActualRank.candidate_positions f hzero hnonzero
  have ha : StrictAnti (fun i : Fin 941 => selectorWeight (tile (f i.succ))) :=
    Fin.strictAnti_iff_succ_lt.mpr hadj
  intro i j hij hi
  cases i using Fin.cases with
  | zero => exact False.elim (hi rfl)
  | succ i =>
      cases j using Fin.cases with
      | zero => exact False.elim (not_lt_of_ge (Fin.zero_le _) hij)
      | succ j => exact ha (by simpa using hij)

end DiophantineConsistency.Sign17KAdjacentRank
#print axioms DiophantineConsistency.Sign17KAdjacentRank.candidate_positions
