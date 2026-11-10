import DiophantineConsistency.Sign17KWeightUnion942

/-! SOURCE-ONLY: generic little-endian ofDigits equals a finite power sum. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KOfDigitsSum
open scoped BigOperators

theorem ofDigits_ofFn_sum (r : ℕ) (n : ℕ) (v : Fin n → ℕ) :
    Nat.ofDigits r (List.ofFn v) = ∑ i : Fin n, v i * r ^ i.val := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, Nat.ofDigits_cons, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    rw [ih]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

end DiophantineConsistency.Sign17KOfDigitsSum
#print axioms DiophantineConsistency.Sign17KOfDigitsSum.ofDigits_ofFn_sum
