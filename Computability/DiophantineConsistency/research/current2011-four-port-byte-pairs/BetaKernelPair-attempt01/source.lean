import CurrentBetaBytes
import KernelRecipe

/-! Checked beta and physical-kernel symbolic byte decoders. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.BetaKernelPair
attribute [local irreducible] CurrentMasks2011.beta CurrentKernel2011.K
  CurrentKernelBytes.recipe CurrentWindowCarry2011.ports

theorem decode_pair :
    ((Nat.ofDigits 256 CurrentBetaBytes.bigBytes.reverse : ℕ) : ℤ) = CurrentWindowCarry2011.ports 0 ∧
    ((Nat.ofDigits 256 ((Nat.digits 256
      (CurrentKernelBytes.recipe (2 ^ 47))).reverse).reverse : ℕ) : ℤ) = CurrentWindowCarry2011.ports 1 :=
  ⟨CurrentBetaBytes.decode_beta, CurrentKernelBytes.decode_kernel⟩

#print axioms decode_pair
end DiophantineConsistency.BetaKernelPair
