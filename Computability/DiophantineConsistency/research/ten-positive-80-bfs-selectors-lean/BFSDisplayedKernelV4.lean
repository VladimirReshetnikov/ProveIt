import BFSDisplayedSelectors

/-! A formal finite-list version of the direct-BFS displayed kernel recipe. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 20000000
set_option exponentiation.threshold 9000
namespace BFSDisplayedKernel
open scoped BigOperators
open CompactSymbolicKernel

theorem values_length : BFSDisplayedSelectors.values.length = 943 := by
  rw [BFSDisplayedSelectors.values_eq_rows_map, List.length_map,
    DirectBFSSymbolicKernel.rows_length]

def displayedSelector (i : Fin 943) : ℕ :=
  BFSDisplayedSelectors.values.get ⟨i.val, by simpa only [values_length] using i.isLt⟩

theorem displayedSelector_eq (i : Fin 943) :
    displayedSelector i = CompactCoefficientMass.selector (DirectBFSSymbolicKernel.row i) := by
  unfold displayedSelector DirectBFSSymbolicKernel.row
  simp only [List.get_eq_getElem, BFSDisplayedSelectors.values_eq_rows_map, List.getElem_map]

def displayedKernel (r : ℕ) : ℕ :=
  r^30+r^62+r^1100+r^2201 +
  (∑ i : Fin 943, displayedSelector i * (r^(4393-i.val)+r^(5495-i.val))) +
  (∑ i : Fin 41, (2^(10+i.val):ℕ) * (r^(4393-position i)+r^(5495-position i))) +
  r^8849

theorem kernel_eq_displayed (r : ℕ) :
    DirectBFSSymbolicKernel.paramKernel r = displayedKernel r := by
  unfold DirectBFSSymbolicKernel.paramKernel displayedKernel
  have hp : r^8807 * r^42 = r^8849 := (Nat.pow_add r 8807 42).symm
  rw [← hp]
  simp only [displayedSelector_eq]

#print axioms BFSDisplayedKernel.kernel_eq_displayed
end BFSDisplayedKernel
