import BFSDisplayedKernelV4

/-! The 41 printed slots and the fully decimal-list BFS kernel formula. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 20000000
namespace BFSDisplayedSlots
open scoped BigOperators

def values : List ℕ := [
  1023, 1024, 1025, 1026, 1027, 1028, 1029, 1030,
  1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020,
  1021, 1003, 1004, 1005, 1006, 1007, 1008, 1009,
  1010, 983, 984, 985, 986, 987, 988, 989,
  990, 991, 1031, 1022, 1011, 992, 1095, 2195,
  3296
]

theorem values_eq_slots : values = CompactSymbolicKernel.slots := by rfl

theorem values_length : values.length = 41 := by
  rw [values_eq_slots, CompactSymbolicKernel.slots_length]

def displayedPosition (i : Fin 41) : ℕ :=
  values.get ⟨i.val, by simpa only [values_length] using i.isLt⟩

theorem displayedPosition_eq (i : Fin 41) :
    displayedPosition i = CompactSymbolicKernel.position i := by
  unfold displayedPosition CompactSymbolicKernel.position
  simp only [List.get_eq_getElem, values_eq_slots]

def displayedKernel (r : ℕ) : ℕ :=
  r^30+r^62+r^1100+r^2201 +
  (∑ i : Fin 943, BFSDisplayedKernel.displayedSelector i * (r^(4393-i.val)+r^(5495-i.val))) +
  (∑ i : Fin 41, (2^(10+i.val):ℕ) * (r^(4393-displayedPosition i)+r^(5495-displayedPosition i))) +
  r^8849

theorem kernel_eq_displayed (r : ℕ) :
    DirectBFSSymbolicKernel.paramKernel r = displayedKernel r := by
  rw [BFSDisplayedKernel.kernel_eq_displayed]
  unfold BFSDisplayedKernel.displayedKernel displayedKernel
  simp only [displayedPosition_eq]

#print axioms BFSDisplayedSlots.kernel_eq_displayed
end BFSDisplayedSlots
