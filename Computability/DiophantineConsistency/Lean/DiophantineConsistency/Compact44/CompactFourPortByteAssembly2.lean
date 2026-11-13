import DiophantineConsistency.Compact44.GenericFourBytePorts
import DiophantineConsistency.Compact44.RetainedBetaBytes
import DiophantineConsistency.Compact44.CompactKernelByteRecipe
import DiophantineConsistency.Compact44.CompactLowByteAssembly
import DiophantineConsistency.Compact44.CompactShiftedHighByteAssembly
import DiophantineConsistency.Compact44.CompactSymbolicPorts

/-! Specialize an abstract four-list tuple lemma without reducing byte lists. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactFourPortByteAssembly2
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
attribute [local irreducible] Nat.ofDigits RetainedBetaBytes.betaBytes CompactKernelByteRecipe.bytes
  CompactLowByteRecipeData.bytes CompactShiftedHighByteWindow.bytes
  CompactFixedBeta.betaNat paramKernel rho lowNat highNat

def bytePorts : Fin 4 → List ℕ :=
  ![RetainedBetaBytes.betaBytes, CompactKernelByteRecipe.bytes,
    CompactLowByteRecipeData.bytes, CompactShiftedHighByteWindow.bytes]

theorem decode_ports :
    (fun j => Nat.ofDigits 256 (bytePorts j)) =
      ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat := by
  change (fun j : Fin 4 => Nat.ofDigits 256
      (![RetainedBetaBytes.betaBytes, CompactKernelByteRecipe.bytes,
        CompactLowByteRecipeData.bytes, CompactShiftedHighByteWindow.bytes] j)) =
      ![CompactFixedBeta.betaNat, paramKernel rho, lowNat, CompactFixedBeta.betaNat + highNat]
  exact GenericFourBytePorts.tuple4 _ _ _ _ _ _ _ _
    RetainedBetaBytes.decode_betaBytes CompactKernelByteRecipe.decode_bytes
    CompactLowByteAssembly.decode_bytes CompactShiftedHighByteAssembly.decode_bytes

#print axioms CompactFourPortByteAssembly2.decode_ports
end CompactFourPortByteAssembly2
