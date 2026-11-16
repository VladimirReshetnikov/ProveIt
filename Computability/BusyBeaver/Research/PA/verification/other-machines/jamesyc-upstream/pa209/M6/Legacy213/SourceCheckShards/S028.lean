module
public import M6.Legacy213.SourceCheck
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace M6.Legacy213.SourceCheckShards.S028
open M6.Legacy213.SourceCheck
theorem chunk0 : rangeCheck 1792 8 = true := by decide +kernel
theorem chunk1 : rangeCheck 1800 8 = true := by decide +kernel
theorem chunk2 : rangeCheck 1808 8 = true := by decide +kernel
theorem chunk3 : rangeCheck 1816 8 = true := by decide +kernel
theorem chunk4 : rangeCheck 1824 8 = true := by decide +kernel
theorem chunk5 : rangeCheck 1832 8 = true := by decide +kernel
theorem chunk6 : rangeCheck 1840 8 = true := by decide +kernel
theorem chunk7 : rangeCheck 1848 8 = true := by decide +kernel
theorem checked : rangeCheck 1792 64 = true := by
  apply List.all_eq_true.mpr
  intro i hi
  have hb : i < 64 := List.mem_range.mp hi
  by_cases h0 : i < 8
  · exact range_sound chunk0 (1792+i) (by omega) (by omega)
  by_cases h1 : i < 16
  · exact range_sound chunk1 (1792+i) (by omega) (by omega)
  by_cases h2 : i < 24
  · exact range_sound chunk2 (1792+i) (by omega) (by omega)
  by_cases h3 : i < 32
  · exact range_sound chunk3 (1792+i) (by omega) (by omega)
  by_cases h4 : i < 40
  · exact range_sound chunk4 (1792+i) (by omega) (by omega)
  by_cases h5 : i < 48
  · exact range_sound chunk5 (1792+i) (by omega) (by omega)
  by_cases h6 : i < 56
  · exact range_sound chunk6 (1792+i) (by omega) (by omega)
  exact range_sound chunk7 (1792+i) (by omega) (by omega)
end M6.Legacy213.SourceCheckShards.S028
