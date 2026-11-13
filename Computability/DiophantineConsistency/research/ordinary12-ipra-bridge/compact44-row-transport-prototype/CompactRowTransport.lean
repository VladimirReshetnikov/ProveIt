import DiophantineConsistency.CompactTableLookup
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
noncomputable section
namespace CompactRowTransport
open DiophantineConsistency CompactRelabelDraft
open DiophantineConsistency.ArithmeticWangTable

theorem row_at (m : ℕ) (hm : m < 942) :
    translated (tileN m) =
      Compact943Data.rows.toArray[rowIndices.toList.getD m 0]?.getD (0,0,0,0) := by
  have hr : m < rowIndices.toList.length := by simpa only [CompactTableLookup.row_length] using hm
  have ho : m < WangTiles942.orderedRows.length := by simpa only [WangTiles942.ordered_count] using hm
  have h := congrArg (fun xs => xs[m]?) full_row_equality
  simp only [mappedOld, selectedNew, List.getElem?_map, getElem?_pos WangTiles942.orderedRows m ho,
    getElem?_pos rowIndices.toList m hr, Option.map_some, Option.some.injEq] at h
  simpa only [tileN, dif_pos hm, WangTiles942.tile, List.getD_eq_getElem?_getD,
    getElem?_pos rowIndices.toList m hr, Option.getD_some] using h
#print axioms CompactRowTransport.row_at
end CompactRowTransport
