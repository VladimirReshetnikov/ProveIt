import BetaKernelPair
import MaskPair

/-! Four symbolic big-endian byte recipes decode to the current ports. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.CurrentFourPortBytes
attribute [local irreducible] CurrentBetaBytes.bigBytes CurrentMCBytes.bigBytes
  CurrentMasks2011.radix CurrentMasks2011.beta CurrentMasks2011.lowPort CurrentMasks2011.highPort
  CurrentKernel2011.K CurrentKernelBytes.recipe CurrentMFRecipe.rho CurrentMFRecipe.maskDigits
  CurrentWindowCarry2011.ports

def bigBytes : Fin 4 → List ℕ :=
  ![CurrentBetaBytes.bigBytes, CurrentKernelBytes.bigBytes,
    CurrentMCBytes.bigBytes, CurrentMFDecoderExplicit.bigBytes]

def decoded : Fin 4 → ℤ := fun j =>
  ((Nat.ofDigits 256 ((bigBytes j).reverse) : ℕ) : ℤ)

private theorem fin4_ext (f g : Fin 4 → ℤ)
    (h0 : f 0 = g 0) (h1 : f 1 = g 1) (h2 : f 2 = g 2) (h3 : f 3 = g 3) : f = g := by
  funext j
  fin_cases j <;> assumption

theorem decoded_eq_ports : decoded = CurrentWindowCarry2011.ports := by
  apply fin4_ext decoded CurrentWindowCarry2011.ports
  · change ((Nat.ofDigits 256 CurrentBetaBytes.bigBytes.reverse : ℕ) : ℤ) = CurrentWindowCarry2011.ports 0
    exact BetaKernelPair.decode_pair.1
  · change ((Nat.ofDigits 256 ((Nat.digits 256
      (CurrentKernelBytes.recipe (2 ^ 47))).reverse).reverse : ℕ) : ℤ) = CurrentWindowCarry2011.ports 1
    exact BetaKernelPair.decode_pair.2
  · change ((Nat.ofDigits 256 CurrentMCBytes.bigBytes.reverse : ℕ) : ℤ) = CurrentWindowCarry2011.ports 2
    exact MaskPair.decode_pair.1
  · change ((Nat.ofDigits 256 ((Nat.digits 256
      (Nat.ofDigits CurrentMFRecipe.rho CurrentMFRecipe.maskDigits +
        (CurrentMFRecipe.rho ^ 2011 - 1))).reverse.reverse) : ℕ) : ℤ) = CurrentWindowCarry2011.ports 3
    exact MaskPair.decode_pair.2

#print axioms decoded_eq_ports
end DiophantineConsistency.CurrentFourPortBytes
