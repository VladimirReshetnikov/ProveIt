import SparseRadix
set_option autoImplicit false
namespace SparseCountBound

theorem coefficient_le_length_mul (terms : List (ℕ × ℕ)) (j B : ℕ)
    (hweights : ∀ t ∈ terms, t.2 ≤ B) :
    SparseRadix.coefficientAt terms j ≤ terms.length * B := by
  induction terms with
  | nil => simp [SparseRadix.coefficientAt]
  | cons t ts ih =>
    have ht : t.2 ≤ B := hweights t (by simp)
    have hs : ∀ u ∈ ts, u.2 ≤ B := by
      intro u hu
      exact hweights u (by simp [hu])
    have hi := ih hs
    by_cases h : t.1 = j
    · simp [SparseRadix.coefficientAt, h, Nat.succ_mul] at *
      omega
    · simp [SparseRadix.coefficientAt, h, Nat.succ_mul] at *
      omega

#print axioms SparseCountBound.coefficient_le_length_mul
end SparseCountBound
