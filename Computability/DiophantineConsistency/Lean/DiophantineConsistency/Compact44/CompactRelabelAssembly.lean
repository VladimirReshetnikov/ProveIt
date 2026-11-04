import DiophantineConsistency.Compact44.CompactRelabelChunk00
import DiophantineConsistency.Compact44.CompactRelabelChunk01
import DiophantineConsistency.Compact44.CompactRelabelChunk02
import DiophantineConsistency.Compact44.CompactRelabelChunk03
import DiophantineConsistency.Compact44.CompactRelabelChunk04Join
import DiophantineConsistency.Compact44.CompactRelabelChunk05Join
import DiophantineConsistency.Compact44.CompactRelabelChunk06Join
import DiophantineConsistency.Compact44.CompactRelabelChunk07Join
import DiophantineConsistency.Compact44.CompactRelabelChunk08Join
import DiophantineConsistency.Compact44.CompactRelabelChunk09Join
import DiophantineConsistency.Compact44.CompactRelabelChunk10Join
import DiophantineConsistency.Compact44.CompactRelabelChunk11Join
import DiophantineConsistency.Compact44.CompactRelabelChunk12Join
import DiophantineConsistency.Compact44.CompactRelabelChunk13Join
import DiophantineConsistency.Compact44.CompactRelabelChunk14
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactRelabelDraft

theorem combine_take_drop {α : Type*} (a b : List α) (n : ℕ)
    (hhead : a.take n = b.take n) (htail : a.drop n = b.drop n) : a = b := by
  calc
    a = a.take n ++ a.drop n := (List.take_append_drop n a).symm
    _ = b.take n ++ b.drop n := by rw [hhead, htail]
    _ = b := List.take_append_drop n b

theorem mapped_length : mappedOld.length = 942 := by
  simp only [mappedOld, List.length_map, DiophantineConsistency.WangTiles942.ordered_count]

theorem selected_length : selectedNew.length = 942 := by decide +kernel

theorem full_row_equality : mappedOld = selectedNew := by
  have hleft : (mappedOld.drop 896).length ≤ 46 := by
    simp only [List.length_drop, mapped_length]; omega
  have hright : (selectedNew.drop 896).length ≤ 46 := by
    simp only [List.length_drop, selected_length]; omega
  have h14 : mappedOld.drop 896 = selectedNew.drop 896 := by
    simpa only [List.take_of_length_le hleft, List.take_of_length_le hright] using chunk_14
  have h13 : mappedOld.drop 832 = selectedNew.drop 832 := by
    apply combine_take_drop _ _ 64 chunk_13
    simpa only [List.drop_drop, show 832 + 64 = 896 by decide] using h14
  have h12 : mappedOld.drop 768 = selectedNew.drop 768 := by
    apply combine_take_drop _ _ 64 chunk_12
    simpa only [List.drop_drop, show 768 + 64 = 832 by decide] using h13
  have h11 : mappedOld.drop 704 = selectedNew.drop 704 := by
    apply combine_take_drop _ _ 64 chunk_11
    simpa only [List.drop_drop, show 704 + 64 = 768 by decide] using h12
  have h10 : mappedOld.drop 640 = selectedNew.drop 640 := by
    apply combine_take_drop _ _ 64 chunk_10
    simpa only [List.drop_drop, show 640 + 64 = 704 by decide] using h11
  have h09 : mappedOld.drop 576 = selectedNew.drop 576 := by
    apply combine_take_drop _ _ 64 chunk_09
    simpa only [List.drop_drop, show 576 + 64 = 640 by decide] using h10
  have h08 : mappedOld.drop 512 = selectedNew.drop 512 := by
    apply combine_take_drop _ _ 64 chunk_08
    simpa only [List.drop_drop, show 512 + 64 = 576 by decide] using h09
  have h07 : mappedOld.drop 448 = selectedNew.drop 448 := by
    apply combine_take_drop _ _ 64 chunk_07
    simpa only [List.drop_drop, show 448 + 64 = 512 by decide] using h08
  have h06 : mappedOld.drop 384 = selectedNew.drop 384 := by
    apply combine_take_drop _ _ 64 chunk_06
    simpa only [List.drop_drop, show 384 + 64 = 448 by decide] using h07
  have h05 : mappedOld.drop 320 = selectedNew.drop 320 := by
    apply combine_take_drop _ _ 64 chunk_05
    simpa only [List.drop_drop, show 320 + 64 = 384 by decide] using h06
  have h04 : mappedOld.drop 256 = selectedNew.drop 256 := by
    apply combine_take_drop _ _ 64 chunk_04
    simpa only [List.drop_drop, show 256 + 64 = 320 by decide] using h05
  have h03 : mappedOld.drop 192 = selectedNew.drop 192 := by
    apply combine_take_drop _ _ 64 chunk_03
    simpa only [List.drop_drop, show 192 + 64 = 256 by decide] using h04
  have h02 : mappedOld.drop 128 = selectedNew.drop 128 := by
    apply combine_take_drop _ _ 64 chunk_02
    simpa only [List.drop_drop, show 128 + 64 = 192 by decide] using h03
  have h01 : mappedOld.drop 64 = selectedNew.drop 64 := by
    apply combine_take_drop _ _ 64 chunk_01
    simpa only [List.drop_drop, show 64 + 64 = 128 by decide] using h02
  have h00 : mappedOld.drop 0 = selectedNew.drop 0 := by
    apply combine_take_drop _ _ 64 chunk_00
    simpa only [List.drop_drop, show 0 + 64 = 64 by decide] using h01
  simpa only [List.drop_zero] using h00
end CompactRelabelDraft
#print axioms CompactRelabelDraft.full_row_equality
