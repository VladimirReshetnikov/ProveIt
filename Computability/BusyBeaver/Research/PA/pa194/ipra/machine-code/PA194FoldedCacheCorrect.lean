import PA194FoldedCache

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194FoldedCacheCorrect
open PA194FoldedCache PA194FoldedRuntimeRows PA194LocalQuotient

theorem rows0 : checkRows 0 8 = true := by decide +kernel
theorem rows8 : checkRows 8 8 = true := by decide +kernel
theorem rows16 : checkRows 16 8 = true := by decide +kernel
theorem rows24 : checkRows 24 8 = true := by decide +kernel
theorem rows32 : checkRows 32 8 = true := by decide +kernel
theorem rows40 : checkRows 40 8 = true := by decide +kernel
theorem rows48 : checkRows 48 8 = true := by decide +kernel
theorem rows56 : checkRows 56 8 = true := by decide +kernel
theorem rows64 : checkRows 64 8 = true := by decide +kernel
theorem rows72 : checkRows 72 8 = true := by decide +kernel
theorem rows80 : checkRows 80 8 = true := by decide +kernel
theorem rows88 : checkRows 88 8 = true := by decide +kernel
theorem rows96 : checkRows 96 8 = true := by decide +kernel
theorem rows104 : checkRows 104 8 = true := by decide +kernel
theorem rows112 : checkRows 112 8 = true := by decide +kernel
theorem rows120 : checkRows 120 8 = true := by decide +kernel
theorem rows128 : checkRows 128 8 = true := by decide +kernel
theorem rows136 : checkRows 136 8 = true := by decide +kernel
theorem rows144 : checkRows 144 8 = true := by decide +kernel
theorem rows152 : checkRows 152 8 = true := by decide +kernel
theorem rows160 : checkRows 160 8 = true := by decide +kernel
theorem rows168 : checkRows 168 8 = true := by decide +kernel
theorem rows176 : checkRows 176 8 = true := by decide +kernel
theorem rows184 : checkRows 184 8 = true := by decide +kernel
theorem rows192 : checkRows 192 3 = true := by decide +kernel

theorem labels_size : labels.length = 195 := by decide +kernel

theorem allRows (j : Nat) (hj : j < labels.length) : agreesAt labels[j] = true := by
  have hbound : j < 195 := labels_size ▸ hj
  by_cases stop0 : j < 8
  · exact checkRows_sound 0 8 j rows0 (by omega) stop0 hj
  by_cases stop8 : j < 16
  · exact checkRows_sound 8 8 j rows8 (by omega) stop8 hj
  by_cases stop16 : j < 24
  · exact checkRows_sound 16 8 j rows16 (by omega) stop16 hj
  by_cases stop24 : j < 32
  · exact checkRows_sound 24 8 j rows24 (by omega) stop24 hj
  by_cases stop32 : j < 40
  · exact checkRows_sound 32 8 j rows32 (by omega) stop32 hj
  by_cases stop40 : j < 48
  · exact checkRows_sound 40 8 j rows40 (by omega) stop40 hj
  by_cases stop48 : j < 56
  · exact checkRows_sound 48 8 j rows48 (by omega) stop48 hj
  by_cases stop56 : j < 64
  · exact checkRows_sound 56 8 j rows56 (by omega) stop56 hj
  by_cases stop64 : j < 72
  · exact checkRows_sound 64 8 j rows64 (by omega) stop64 hj
  by_cases stop72 : j < 80
  · exact checkRows_sound 72 8 j rows72 (by omega) stop72 hj
  by_cases stop80 : j < 88
  · exact checkRows_sound 80 8 j rows80 (by omega) stop80 hj
  by_cases stop88 : j < 96
  · exact checkRows_sound 88 8 j rows88 (by omega) stop88 hj
  by_cases stop96 : j < 104
  · exact checkRows_sound 96 8 j rows96 (by omega) stop96 hj
  by_cases stop104 : j < 112
  · exact checkRows_sound 104 8 j rows104 (by omega) stop104 hj
  by_cases stop112 : j < 120
  · exact checkRows_sound 112 8 j rows112 (by omega) stop112 hj
  by_cases stop120 : j < 128
  · exact checkRows_sound 120 8 j rows120 (by omega) stop120 hj
  by_cases stop128 : j < 136
  · exact checkRows_sound 128 8 j rows128 (by omega) stop128 hj
  by_cases stop136 : j < 144
  · exact checkRows_sound 136 8 j rows136 (by omega) stop136 hj
  by_cases stop144 : j < 152
  · exact checkRows_sound 144 8 j rows144 (by omega) stop144 hj
  by_cases stop152 : j < 160
  · exact checkRows_sound 152 8 j rows152 (by omega) stop152 hj
  by_cases stop160 : j < 168
  · exact checkRows_sound 160 8 j rows160 (by omega) stop160 hj
  by_cases stop168 : j < 176
  · exact checkRows_sound 168 8 j rows168 (by omega) stop168 hj
  by_cases stop176 : j < 184
  · exact checkRows_sound 176 8 j rows176 (by omega) stop176 hj
  by_cases stop184 : j < 192
  · exact checkRows_sound 184 8 j rows184 (by omega) stop184 hj
  exact checkRows_sound 192 3 j rows192 (by omega) (by omega) hj

theorem cachedMachine_correct : cachedMachine = machine := by
  funext q b
  by_cases hq : q ∈ labels
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hq
    have hf := Bool.and_eq_true_iff.mp (allRows j hj)
    cases b
    · exact beq_iff_eq.mp hf.1
    · exact beq_iff_eq.mp hf.2
  · have hnone := PA194FoldedCache.outside q b hq
    have hd : denseControl q = 195 := by
      unfold denseControl
      rw [List.idxOf_eq_length_iff.mpr hq,labels_size]
    rw [hnone,machine,hd]
    cases b <;> rfl

#print axioms cachedMachine_correct
end PA194FoldedCacheCorrect
