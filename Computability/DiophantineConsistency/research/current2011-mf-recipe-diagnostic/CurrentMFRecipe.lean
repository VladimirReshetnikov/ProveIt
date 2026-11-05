import FreshModel106

/-! Canonical base-256 bytes of the explicitly beta-shifted high mask. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.CurrentMFRecipe

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


#print axioms maskDigits_eq
#print axioms highPort_eq
#print axioms beta_eq
end DiophantineConsistency.CurrentMFRecipe
