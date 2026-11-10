import DiophantineConsistency.Sign17KRadixReversal

/-! SOURCE ONLY. Algebra for the exponent-1004 K sentinel collision. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KSentinelCollision
open scoped BigOperators

theorem shifted_reversed (r n shift : ℕ) (v : Fin n → ℕ) :
    r ^ shift * Nat.ofDigits r (List.ofFn (fun i => v i.rev)) =
      ∑ i : Fin n, v i * r ^ (shift + (n - (i.val + 1))) := by
  rw [Sign17KRadixReversal.ofDigits_reversed, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_add]
  ac_rfl

theorem shifted_986 (r : ℕ) (v : Fin 986 → ℕ) :
    r ^ 20 * Nat.ofDigits r (List.ofFn (fun i => v i.rev)) =
      ∑ i : Fin 986, v i * r ^ (1005 - i.val) := by
  rw [shifted_reversed]
  apply Finset.sum_congr rfl
  intro i _
  have hi := i.isLt
  have he : 20 + (986 - (i.val + 1)) = 1005 - i.val := by omega
  rw [he]

theorem middle_sentinel (r : ℕ) (v : Fin 986 → ℕ) :
    r ^ 20 * Nat.ofDigits r (List.ofFn
      (fun i : Fin 986 => v i.rev + if i = ⟨984, by decide⟩ then 1 else 0)) =
      (∑ i : Fin 986, v i * r ^ (1005 - i.val)) + r ^ 1004 := by
  rw [Sign17KRadixReversal.ofDigits_increment, Nat.mul_add, shifted_986]
  rw [← pow_add]
  rfl

end DiophantineConsistency.Sign17KSentinelCollision
#print axioms DiophantineConsistency.Sign17KSentinelCollision.middle_sentinel
