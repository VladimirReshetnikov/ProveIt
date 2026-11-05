import FreshModel106

/-! Big-endian beta byte recipe and its decoding into the current2011 port. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.CurrentBetaBytes

theorem decode_max_bytes_add_one (n top : ℕ) :
    Nat.ofDigits 256 (List.replicate n 255 ++ [top]) + 1 = 256^n * (top + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, List.cons_append, Nat.ofDigits, pow_succ']
      calc
        255 + 256 * Nat.ofDigits 256 (List.replicate n 255 ++ [top]) + 1 =
            256 * (Nat.ofDigits 256 (List.replicate n 255 ++ [top]) + 1) := by omega
        _ = 256 * (256^n * (top + 1)) := by rw [ih]
        _ = (256 * 256^n) * (top + 1) := by rw [Nat.mul_assoc]

/-- Big-endian bytes: five high bits set followed by 11,814 full bytes. -/
def bigBytes : List ℕ := 31 :: List.replicate 11814 255

theorem decode_beta :
    (Nat.ofDigits 256 bigBytes.reverse : ℤ) = CurrentWindowCarry2011.ports 0 := by
  have hp : (256 : ℕ)^11814 * (31 + 1) = CurrentMasks2011.radix^2011 := by
    unfold CurrentMasks2011.radix
    rw [show (256:ℕ) = 2^8 by norm_num, show (31+1:ℕ) = 2^5 by norm_num,
        ← pow_mul, ← pow_add, ← pow_mul]
  have h := decode_max_bytes_add_one 11814 31
  rw [hp] at h
  have hb : Nat.ofDigits 256 (List.replicate 11814 255 ++ [31]) = CurrentMasks2011.beta := by
    unfold CurrentMasks2011.beta
    omega
  change (Nat.ofDigits 256 bigBytes.reverse : ℤ) = (CurrentMasks2011.beta : ℤ)
  rw [show bigBytes.reverse = List.replicate 11814 255 ++ [31] by
    simp only [bigBytes, List.reverse_cons, List.reverse_replicate]]
  exact_mod_cast hb

#print axioms decode_max_bytes_add_one
#print axioms decode_beta
end DiophantineConsistency.CurrentBetaBytes
