import SparseRadix
set_option autoImplicit false
namespace SparseAggregateBasic

theorem coefficient_le_total (terms : List (ℕ × ℕ)) (j : ℕ) :
    SparseRadix.coefficientAt terms j ≤ (terms.map Prod.snd).sum := by
  induction terms with
  | nil => simp [SparseRadix.coefficientAt]
  | cons t ts ih =>
    by_cases h : t.1 = j
    · simp [SparseRadix.coefficientAt, h] at *
      omega
    · simp [SparseRadix.coefficientAt, h] at *
      omega

#print axioms SparseAggregateBasic.coefficient_le_total
end SparseAggregateBasic
