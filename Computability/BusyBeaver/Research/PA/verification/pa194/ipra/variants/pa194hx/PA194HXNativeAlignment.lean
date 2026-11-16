import PA194HXNativeLabels
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194HXNativeAlignment
open PA194HXNativeLabels

theorem block_sound (base count q : Nat) (h : blockCheck base count = true)
    (lo : base ≤ q) (hi : q < base+count) : rowCheck q = true := by
  have hh := List.all_eq_true.mp h (q-base) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le lo] using hh

theorem allRows (q : Nat) (hq : q < 194) : rowCheck q = true := by
  by_cases stop0 : q < 8
  · exact block_sound 0 8 q rows0 (by omega) stop0
  by_cases stop8 : q < 16
  · exact block_sound 8 8 q rows8 (by omega) stop8
  by_cases stop16 : q < 24
  · exact block_sound 16 8 q rows16 (by omega) stop16
  by_cases stop24 : q < 32
  · exact block_sound 24 8 q rows24 (by omega) stop24
  by_cases stop32 : q < 40
  · exact block_sound 32 8 q rows32 (by omega) stop32
  by_cases stop40 : q < 48
  · exact block_sound 40 8 q rows40 (by omega) stop40
  by_cases stop48 : q < 56
  · exact block_sound 48 8 q rows48 (by omega) stop48
  by_cases stop56 : q < 64
  · exact block_sound 56 8 q rows56 (by omega) stop56
  by_cases stop64 : q < 72
  · exact block_sound 64 8 q rows64 (by omega) stop64
  by_cases stop72 : q < 80
  · exact block_sound 72 8 q rows72 (by omega) stop72
  by_cases stop80 : q < 88
  · exact block_sound 80 8 q rows80 (by omega) stop80
  by_cases stop88 : q < 96
  · exact block_sound 88 8 q rows88 (by omega) stop88
  by_cases stop96 : q < 104
  · exact block_sound 96 8 q rows96 (by omega) stop96
  by_cases stop104 : q < 112
  · exact block_sound 104 8 q rows104 (by omega) stop104
  by_cases stop112 : q < 120
  · exact block_sound 112 8 q rows112 (by omega) stop112
  by_cases stop120 : q < 128
  · exact block_sound 120 8 q rows120 (by omega) stop120
  by_cases stop128 : q < 136
  · exact block_sound 128 8 q rows128 (by omega) stop128
  by_cases stop136 : q < 144
  · exact block_sound 136 8 q rows136 (by omega) stop136
  by_cases stop144 : q < 152
  · exact block_sound 144 8 q rows144 (by omega) stop144
  by_cases stop152 : q < 160
  · exact block_sound 152 8 q rows152 (by omega) stop152
  by_cases stop160 : q < 168
  · exact block_sound 160 8 q rows160 (by omega) stop160
  by_cases stop168 : q < 176
  · exact block_sound 168 8 q rows168 (by omega) stop168
  by_cases stop176 : q < 184
  · exact block_sound 176 8 q rows176 (by omega) stop176
  by_cases stop184 : q < 192
  · exact block_sound 184 8 q rows184 (by omega) stop184
  exact block_sound 192 2 q rows192 (by omega) (by omega)

/-- For every working dense HX control and read bit, the cached native
    row is precisely the actual HX literal row transported through labels. -/
theorem step_aligned (q : Nat) (b : Bool) (hq : q < 194) :
    PA194HXContracts.cachedMachine (nativeOf q) b = mapped q b := by
  have h := Bool.and_eq_true_iff.mp (allRows q hq)
  cases b
  · exact beq_iff_eq.mp h.1
  · exact beq_iff_eq.mp h.2

theorem terminal_native : PA194HXContracts.cachedMachine 254 false = none ∧
    PA194HXContracts.cachedMachine 254 true = none := by decide +kernel

#print axioms step_aligned
#print axioms terminal_native
end PA194HXNativeAlignment
