import RetainedBetaBytes
import CompactKernelByteRecipe
import CompactLowByteAssembly
import CompactShiftedHighByteAssembly
import DiophantineConsistency.CompactSymbolicPorts

/-! Join four closed natural-byte recipes to the fixed symbolic port tuple. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactFourPortByteAssembly
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
attribute [local irreducible] RetainedBetaBytes.betaBytes CompactKernelByteRecipe.bytes
  CompactLowByteRecipeData.bytes CompactShiftedHighByteWindow.bytes
  CompactFixedBeta.betaNat paramKernel rho lowNat highNat

def bytePorts : Fin 4 → List ℕ :=
  ![RetainedBetaBytes.betaBytes, CompactKernelByteRecipe.bytes,
    CompactLowByteRecipeData.bytes, CompactShiftedHighByteWindow.bytes]

theorem decode_ports :
    (fun j => Nat.ofDigits 256 (bytePorts j)) =
      ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat := by
  funext j
  fin_cases j
  · change Nat.ofDigits 256 RetainedBetaBytes.betaBytes = CompactFixedBeta.betaNat
    exact RetainedBetaBytes.decode_betaBytes
  · change Nat.ofDigits 256 CompactKernelByteRecipe.bytes = paramKernel rho
    exact CompactKernelByteRecipe.decode_bytes
  · change Nat.ofDigits 256 CompactLowByteRecipeData.bytes = lowNat
    exact CompactLowByteAssembly.decode_bytes
  · change Nat.ofDigits 256 CompactShiftedHighByteWindow.bytes =
      CompactFixedBeta.betaNat + highNat
    exact CompactShiftedHighByteAssembly.decode_bytes

#print axioms CompactFourPortByteAssembly.decode_ports
end CompactFourPortByteAssembly
