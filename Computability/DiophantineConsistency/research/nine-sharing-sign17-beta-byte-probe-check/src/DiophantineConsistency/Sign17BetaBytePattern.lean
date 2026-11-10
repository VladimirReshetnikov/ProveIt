import DiophantineConsistency.Sign17ExactDegree

/-! SOURCE-ONLY: symbolic big-endian beta pattern, not a file/gzip binding. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17BetaBytePattern

theorem ff_digits_add_one (n : ℕ) :
    Nat.ofDigits 256 (List.replicate n 255) + 1 = 256 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, Nat.ofDigits_cons, pow_succ]
    omega

theorem beta_pattern :
    Nat.ofDigits 256 ((31 :: List.replicate 11814 255).reverse) = CurrentMasks2011.beta := by
  have hd := ff_digits_add_one 11814
  have hp : ((2 : ℕ) ^ 47) ^ 2011 = 256 ^ 11814 * 32 := by
    calc
      ((2 : ℕ) ^ 47) ^ 2011 = 2 ^ (47 * 2011) := by rw [pow_mul]
      _ = 2 ^ (8 * 11814 + 5) := by congr 1
      _ = (2 ^ 8) ^ 11814 * 2 ^ 5 := by rw [pow_mul, pow_add]
      _ = 256 ^ 11814 * 32 := by
        rw [show (2 : ℕ) ^ 8 = 256 by decide, show (2 : ℕ) ^ 5 = 32 by decide]
  have hdecoded : Nat.ofDigits 256 ((31 :: List.replicate 11814 255).reverse) + 1 =
      ((2 : ℕ) ^ 47) ^ 2011 := by
    rw [List.reverse_cons, List.reverse_replicate, Nat.ofDigits_append,
      List.length_replicate, Nat.ofDigits_singleton]
    omega
  change Nat.ofDigits 256 ((31 :: List.replicate 11814 255).reverse) =
    ((2 : ℕ) ^ 47) ^ 2011 - 1
  omega

theorem current_port0_pattern :
    (Nat.ofDigits 256 ((31 :: List.replicate 11814 255).reverse) : ℤ) =
      CurrentWindowCarry2011.ports 0 := by
  change (Nat.ofDigits 256 ((31 :: List.replicate 11814 255).reverse) : ℤ) =
    (CurrentMasks2011.beta : ℤ)
  rw [beta_pattern]

end DiophantineConsistency.Sign17BetaBytePattern
#print axioms DiophantineConsistency.Sign17BetaBytePattern.ff_digits_add_one
#print axioms DiophantineConsistency.Sign17BetaBytePattern.beta_pattern
#print axioms DiophantineConsistency.Sign17BetaBytePattern.current_port0_pattern
