import DiophantineConsistency.Compact44.CompactShiftedHighDigits
import DiophantineConsistency.Compact44.ByteWindow
import Mathlib.Data.List.GetD

/-! A closed byte recipe using local windows of the once-shifted high digits. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactShiftedHighByteWindow
open CompactShiftedHighDigits

def byteAt (j : ℕ) : ℕ :=
  (PaddedRadixDigits.digit shiftedDigits ((8*j)/67) / 2^((8*j)%67) +
   PaddedRadixDigits.digit shiftedDigits ((8*j)/67+1) * 2^(67-(8*j)%67)) % 256

theorem byteAt_eq (j : ℕ) : byteAt j =
    ((CompactFixedBeta.betaNat + CompactSymbolicPorts.highNat) / 256^j) % 256 := by
  have hp : (256:ℕ)^j = 2^(8*j) := by
    rw [show (256:ℕ) = 2^8 by norm_num, ← pow_mul]
  rw [hp]
  have h := ByteWindow.byte shiftedDigits shifted_digits_bounded j
  rw [← shifted_value] at h
  exact h.symm

def bytes : List ℕ := (List.range 73759).map byteAt

theorem bytes_length : bytes.length = 73759 := by simp [bytes]

theorem bytes_getD (j : ℕ) (hj : j < 73759) : bytes.getD j 0 = byteAt j := by
  unfold bytes
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp only [List.getElem_map, List.getElem_range]

theorem bytes_windows (j : ℕ) (hj : j < bytes.length) : bytes.getD j 0 =
    ((CompactFixedBeta.betaNat + CompactSymbolicPorts.highNat) / 256^j) % 256 := by
  rw [bytes_length] at hj
  rw [bytes_getD j hj]
  exact byteAt_eq j

#print axioms CompactShiftedHighByteWindow.byteAt_eq
#print axioms CompactShiftedHighByteWindow.bytes_windows
end CompactShiftedHighByteWindow
