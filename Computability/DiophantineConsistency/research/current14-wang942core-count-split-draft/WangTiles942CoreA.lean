import DiophantineConsistency.WangTiles942TableData
import DiophantineConsistency.WangTiles942Data
import Mathlib.Tactic

/-!
# The exact 942 indexed Wang tiles on the maintained decimal page

All action-cache entries are checked against the actual decimal decoder.
The row families below are the complete printed table; the target sets
retain the halting target 215. Color names use the true packed order
west, north, east, south. No tiling or consistency equivalence is assumed.
-/

namespace DiophantineConsistency.WangTiles942

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option exponentiation.threshold 1024

/-- All transition rows use the actual decimal action, not an unproved table. -/
theorem transitionRow_eq_decoded (j : Fin 430) : transitionRow j =
    (j.val + 1, ⟨(1-(DecimalMachine215.action j.val).2.1.toNat) *
      rail false (DecimalMachine215.action j.val).2.2,
      headColor (j.val/2) (j.val%2),
      (DecimalMachine215.action j.val).2.1.toNat *
        rail true (DecimalMachine215.action j.val).2.2,
      (DecimalMachine215.action j.val).1.toNat⟩) := by
  unfold transitionRow
  rw [action_eq_decoder]

theorem ordered_rows_perm : orderedRows.Perm indexedRows := by
  unfold orderedRows indexedRows
  exact ((((List.Perm.refl _).append (List.Perm.refl _)).append
    List.perm_append_comm).append List.perm_append_comm).append (List.Perm.refl _)

theorem row_indices_nodup : (indexedRows.map Prod.fst).Nodup := by
  have h : (orderedRows.map Prod.fst).Nodup := by
    rw [row_indices_exact]
    exact List.nodup_range
  exact (ordered_rows_perm.map Prod.fst).nodup_iff.mp h

theorem row_count : indexedRows.length = 942 := by
  rw [← ordered_rows_perm.length_eq, ordered_count]

end DiophantineConsistency.WangTiles942
