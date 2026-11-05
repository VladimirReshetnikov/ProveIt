import CurrentBetaBytes
import KernelRecipe
import CurrentMCBytes
import CurrentMFDecoderExplicit

/-! Four separately checked symbolic big-endian byte recipes decode to the current ports. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.CurrentFourPortBytes
attribute [local irreducible] CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentKernel2011.K
  CurrentKernelBytes.recipe CurrentMFRecipe.rho CurrentMFRecipe.maskDigits
  CurrentWindowCarry2011.ports

def bigBytes : Fin 4 → List ℕ :=
  ![CurrentBetaBytes.bigBytes, CurrentKernelBytes.bigBytes,
    CurrentMCBytes.bigBytes, CurrentMFDecoderExplicit.bigBytes]

def decoded : Fin 4 → ℤ := fun j =>
  ((Nat.ofDigits 256 ((bigBytes j).reverse) : ℕ) : ℤ)

theorem decoded_eq_ports : decoded = CurrentWindowCarry2011.ports := by
  funext j
  fin_cases j
  · change (Nat.ofDigits 256 CurrentBetaBytes.bigBytes.reverse : ℤ) = CurrentWindowCarry2011.ports 0
    exact CurrentBetaBytes.decode_beta
  · change ((Nat.ofDigits 256 ((Nat.digits 256
      (CurrentKernelBytes.recipe (2 ^ 47))).reverse).reverse : ℕ) : ℤ) = CurrentWindowCarry2011.ports 1
    exact CurrentKernelBytes.decode_kernel
  · change ((Nat.ofDigits 256 CurrentMCBytes.bigBytes.reverse : ℕ) : ℤ) = CurrentWindowCarry2011.ports 2
    exact CurrentMCBytes.decode_mc
  · change ((Nat.ofDigits 256 ((Nat.digits 256
      (Nat.ofDigits CurrentMFRecipe.rho CurrentMFRecipe.maskDigits +
        (CurrentMFRecipe.rho ^ 2011 - 1))).reverse.reverse) : ℕ) : ℤ) = CurrentWindowCarry2011.ports 3
    exact CurrentMFDecoderExplicit.decode_mf

#print axioms decoded_eq_ports
end DiophantineConsistency.CurrentFourPortBytes
