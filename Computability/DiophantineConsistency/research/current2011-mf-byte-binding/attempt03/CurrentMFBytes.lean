import FreshModel106

/-! Canonical base-256 bytes of the explicitly beta-shifted high mask. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.CurrentMFBytes

def rho : ℕ := 2^47

/-- Little-endian base-2^47 digits of the unshifted high mask. -/
def maskDigits : List ℕ :=
  (4 :: (List.replicate 916 8 ++ List.replicate 43 0 ++ List.replicate 9 1 ++
    List.replicate 18 0 ++ List.replicate 8 1 ++ List.replicate 9 0 ++ [1, 2^45-4])) ++
      List.replicate 1005 0

theorem rho_eq : rho = CurrentMasks2011.radix := rfl

theorem maskDigits_eq : maskDigits = CurrentMasks2011.highDigits := by
  unfold maskDigits CurrentMasks2011.highDigits CurrentMasks2011.highPrefix
  rfl

theorem highPort_eq : Nat.ofDigits rho maskDigits = CurrentMasks2011.highPort := by
  simp only [rho_eq, maskDigits_eq, CurrentMasks2011.highPort]

theorem beta_eq : rho^2011 - 1 = CurrentMasks2011.beta := by
  simp only [rho_eq, CurrentMasks2011.beta]

attribute [local irreducible] rho maskDigits CurrentMasks2011.radix
  CurrentMasks2011.highPort CurrentMasks2011.beta

/-- The beta shift is applied exactly once. -/
def shiftedValue : ℕ := Nat.ofDigits rho maskDigits + (rho^2011 - 1)

theorem shiftedValue_eq_port : (shiftedValue : ℤ) = CurrentWindowCarry2011.ports 3 := by
  unfold shiftedValue
  rw [highPort_eq, beta_eq]
  change ((CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ) : ℤ) =
    (CurrentMasks2011.highPort : ℤ) + (CurrentMasks2011.beta : ℤ)
  exact Nat.cast_add _ _

attribute [local irreducible] shiftedValue

/-- Canonical big-endian base-256 conversion of the shifted mask. -/
def bigBytes : List ℕ := (Nat.digits 256 shiftedValue).reverse

theorem decode_mf :
    ((Nat.ofDigits 256 bigBytes.reverse : ℕ) : ℤ) = CurrentWindowCarry2011.ports 3 := by
  rw [bigBytes, List.reverse_reverse, Nat.ofDigits_digits]
  exact shiftedValue_eq_port

#print axioms shiftedValue_eq_port
#print axioms decode_mf
end DiophantineConsistency.CurrentMFBytes
