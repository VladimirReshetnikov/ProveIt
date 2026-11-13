import CurrentMCBytes
import CurrentMFDecoderExplicit

/-! Checked low and once-shifted high symbolic byte decoders. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.MaskPair
attribute [local irreducible] CurrentMCBytes.bigBytes CurrentMasks2011.beta CurrentMasks2011.radix
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMFRecipe.rho CurrentMFRecipe.maskDigits
  CurrentWindowCarry2011.ports

theorem decode_pair :
    ((Nat.ofDigits 256 CurrentMCBytes.bigBytes.reverse : ℕ) : ℤ) = CurrentWindowCarry2011.ports 2 ∧
    ((Nat.ofDigits 256 ((Nat.digits 256
      (Nat.ofDigits CurrentMFRecipe.rho CurrentMFRecipe.maskDigits +
        (CurrentMFRecipe.rho ^ 2011 - 1))).reverse.reverse) : ℕ) : ℤ) = CurrentWindowCarry2011.ports 3 :=
  ⟨CurrentMCBytes.decode_mc, CurrentMFDecoderExplicit.decode_mf⟩

#print axioms decode_pair
end DiophantineConsistency.MaskPair
