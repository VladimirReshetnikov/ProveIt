import DiophantineConsistency.SparseBorrowCarry

open DiophantineConsistency.SparseBorrowCarry
open Jones1982 Polynomial

private def negativeLower (i : ℕ) : ℤ := if i=0 then -1 else if i=2 then 1 else 0
private def negativeMarked (i : ℕ) : ℤ := if i=1 then -1 else if i=2 then 1 else 0
private def positiveMarked (i : ℕ) : ℤ := if i=1 then 1 else if i=2 then 1 else 0

/-- A negative lower coefficient creates an incoming -1 borrow at a zero target. -/
example : borrow (raw {1} negativeLower) 1 = -1 := by decide
example : digit 8 (raw {1} negativeLower) 1 = 0 := by decide
example : borrow (raw {1} negativeLower) 3 = 0 := by decide
example : value 8 3 {1} negativeLower = 134 := by decide
example : τ 2 (value 8 3 {1} negativeLower).toNat (mask 8 {1})=0 := by decide

/-- Either sign of a nonzero monitored coefficient meets the sparse mask. -/
example : digit 8 (raw {1} negativeMarked) 1 = 7 := by decide
example : τ 2 (value 8 3 {1} negativeMarked).toNat (mask 8 {1})≠0 := by decide
example : digit 8 (raw {1} positiveMarked) 1 = 3 := by decide
example : τ 2 (value 8 3 {1} positiveMarked).toNat (mask 8 {1})≠0 := by decide

/-- Target zero has no incoming borrow; its padding bit remains one. -/
example : digit 8 (raw {0} negativeMarked) 0 = 1 := by decide
example : τ 2 (value 8 3 {0} negativeMarked).toNat (mask 8 {0})=0 := by decide

/-- The exact polynomial API accepts negative coefficients and a nonzero value. -/
private noncomputable def p : ℤ[X] := X^2-C 1

example : τ 2 (2*p.eval 8+(8:ℤ)).toNat (mask 8 {1})=0 := by
  have hp : p.natDegree<3 := by
    have hd : p.natDegree≤2 := by
      calc p.natDegree ≤ max ((X^2:ℤ[X]).natDegree) (C 1:ℤ[X]).natDegree := natDegree_sub_le _ _
           _=2 := by simp
    omega
  have hb : ∀ i<3,|p.coeff i|<(8:ℤ)/4 := by
    intro i hi
    interval_cases i <;> norm_num [p,Polynomial.coeff_one]
  have hv : 0≤2*p.eval (8:ℤ)+∑ i∈({1}:Finset ℕ),(8:ℤ)^i := by norm_num [p,Polynomial.coeff_one]
  have h := tau_polynomial_iff (B:=8) (t:=3) (n:=3) (by decide) (by decide)
    {1} (by intro i hi; simp only [Finset.mem_singleton] at hi; omega) p hp hb hv
  have hz : ∀ i∈({1}:Finset ℕ),p.coeff i=0 := by simp [p,Polynomial.coeff_one]
  simpa [mask] using h.mpr hz

#print axioms borrow
#print axioms word_eq_toNat
#print axioms marked_digit_lt_two_iff
#print axioms tau_sparse_iff
#print axioms value_eq_polynomial
#print axioms tau_polynomial_iff
