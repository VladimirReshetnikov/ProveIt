import DiophantineConsistency.Compact44.CompactFixedBeta
import Mathlib.Data.Nat.Digits.Defs

/-! Little-endian byte recipe for the compact symbolic beta. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace RetainedBetaBytes

/-- `n` low bytes of 255, followed by one unrestricted top digit. -/
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

/-- Compact run-length representation of the exact little-endian byte list. -/
def betaBytes : List ℕ := List.replicate 73758 255 ++ [31]

theorem betaBytes_length : betaBytes.length = 73759 := by
  unfold betaBytes
  rw [List.length_append, List.length_replicate]
  rfl

theorem betaBytes_valid : ∀ x ∈ betaBytes, x < 256 := by
  intro x hx
  unfold betaBytes at hx
  rw [List.mem_append, List.mem_replicate, List.mem_singleton] at hx
  rcases hx with (⟨_, rfl⟩ | rfl) <;> decide

attribute [local irreducible] betaBytes

theorem eq_sub_one_of_add_one (a b : ℕ) (h : a + 1 = b) : a = b - 1 := by
  omega

/-- Decode the symbolic byte recipe without evaluating the 590,069-bit integer. -/
theorem decode_betaBytes : Nat.ofDigits 256 betaBytes = CompactFixedBeta.betaNat := by
  have hp : (256:ℕ)^73758 * (31+1) = 2^(67*8807) := by
    rw [show (256:ℕ) = 2^8 by norm_num, show (31+1:ℕ) = 2^5 by norm_num,
        ← pow_mul, ← pow_add]
  have h := decode_max_bytes_add_one 73758 31
  rw [← betaBytes] at h
  rw [hp] at h
  unfold CompactFixedBeta.betaNat
  exact eq_sub_one_of_add_one _ _ h

#print axioms RetainedBetaBytes.decode_max_bytes_add_one
#print axioms RetainedBetaBytes.decode_betaBytes
end RetainedBetaBytes
