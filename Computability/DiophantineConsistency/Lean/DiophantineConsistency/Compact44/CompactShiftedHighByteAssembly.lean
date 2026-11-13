import DiophantineConsistency.Compact44.CompactShiftedHighByteWindow
import DiophantineConsistency.Compact44.CompactShiftedHighBound
import DiophantineConsistency.Compact44.RadixWindowReconstruction

/-! Reconstruct the once-shifted symbolic high port from its closed byte recipe. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactShiftedHighByteAssembly
open CompactShiftedHighByteWindow
attribute [local irreducible] bytes CompactFixedBeta.betaNat CompactSymbolicPorts.highNat

theorem decode_bytes : Nat.ofDigits 256 bytes =
    CompactFixedBeta.betaNat + CompactSymbolicPorts.highNat := by
  apply RadixWindowReconstruction.ofDigits_eq_of_windows 256 (by decide)
  · rw [bytes_length]
    exact CompactShiftedHighBound.shifted_lt_byte_power
  · exact bytes_windows

#print axioms CompactShiftedHighByteAssembly.decode_bytes
end CompactShiftedHighByteAssembly
