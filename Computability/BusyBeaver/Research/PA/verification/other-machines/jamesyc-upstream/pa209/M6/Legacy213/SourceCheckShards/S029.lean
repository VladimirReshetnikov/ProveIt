module
public import M6.Legacy213.SourceCheck
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace M6.Legacy213.SourceCheckShards.S029
open M6.Legacy213.SourceCheck
theorem chunk0 : rangeCheck 1856 8 = true := by decide +kernel
theorem chunk1 : rangeCheck 1864 8 = true := by decide +kernel
theorem chunk2 : rangeCheck 1872 8 = true := by decide +kernel
theorem chunk3 : rangeCheck 1880 8 = true := by decide +kernel
theorem chunk4 : rangeCheck 1888 8 = true := by decide +kernel
theorem chunk5 : rangeCheck 1896 8 = true := by decide +kernel
theorem chunk6 : rangeCheck 1904 8 = true := by decide +kernel
theorem chunk7 : rangeCheck 1912 8 = true := by decide +kernel
theorem checked : rangeCheck 1856 64 = true := by
  apply List.all_eq_true.mpr
  intro i hi
  have hb : i < 64 := List.mem_range.mp hi
  by_cases h0 : i < 8
  · exact range_sound chunk0 (1856+i) (by omega) (by omega)
  by_cases h1 : i < 16
  · exact range_sound chunk1 (1856+i) (by omega) (by omega)
  by_cases h2 : i < 24
  · exact range_sound chunk2 (1856+i) (by omega) (by omega)
  by_cases h3 : i < 32
  · exact range_sound chunk3 (1856+i) (by omega) (by omega)
  by_cases h4 : i < 40
  · exact range_sound chunk4 (1856+i) (by omega) (by omega)
  by_cases h5 : i < 48
  · exact range_sound chunk5 (1856+i) (by omega) (by omega)
  by_cases h6 : i < 56
  · exact range_sound chunk6 (1856+i) (by omega) (by omega)
  exact range_sound chunk7 (1856+i) (by omega) (by omega)
end M6.Legacy213.SourceCheckShards.S029
