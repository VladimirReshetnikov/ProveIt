import FourByteGeneric
import BetaKernelPair
import MaskPair

/-! The four symbolic big-endian byte recipes decode to the current ports. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.CurrentFourPortBytes
attribute [local irreducible] CurrentBetaBytes.bigBytes CurrentMCBytes.bigBytes
  CurrentMasks2011.radix CurrentMasks2011.beta CurrentMasks2011.lowPort CurrentMasks2011.highPort
  CurrentKernel2011.K CurrentKernelBytes.recipe CurrentMFRecipe.rho CurrentMFRecipe.maskDigits
  CurrentWindowCarry2011.ports

def bigBytes : Fin 4 → List ℕ :=
  FourByteGeneric.bytes CurrentBetaBytes.bigBytes ((Nat.digits 256 (CurrentKernelBytes.recipe (2 ^ 47))).reverse)
    CurrentMCBytes.bigBytes ((Nat.digits 256 (Nat.ofDigits CurrentMFRecipe.rho CurrentMFRecipe.maskDigits + (CurrentMFRecipe.rho ^ 2011 - 1))).reverse)

def decoded : Fin 4 → ℤ :=
  FourByteGeneric.decoded CurrentBetaBytes.bigBytes ((Nat.digits 256 (CurrentKernelBytes.recipe (2 ^ 47))).reverse)
    CurrentMCBytes.bigBytes ((Nat.digits 256 (Nat.ofDigits CurrentMFRecipe.rho CurrentMFRecipe.maskDigits + (CurrentMFRecipe.rho ^ 2011 - 1))).reverse)

theorem decoded_apply (j : Fin 4) : decoded j =
    ((Nat.ofDigits 256 ((bigBytes j).reverse) : ℕ) : ℤ) := rfl

theorem decoded_eq_ports : decoded = CurrentWindowCarry2011.ports :=
  FourByteGeneric.assemble CurrentBetaBytes.bigBytes ((Nat.digits 256 (CurrentKernelBytes.recipe (2 ^ 47))).reverse)
    CurrentMCBytes.bigBytes ((Nat.digits 256 (Nat.ofDigits CurrentMFRecipe.rho CurrentMFRecipe.maskDigits + (CurrentMFRecipe.rho ^ 2011 - 1))).reverse) CurrentWindowCarry2011.ports
    BetaKernelPair.decode_pair.1 BetaKernelPair.decode_pair.2
    MaskPair.decode_pair.1 MaskPair.decode_pair.2

#print axioms decoded_apply
#print axioms decoded_eq_ports
end DiophantineConsistency.CurrentFourPortBytes
