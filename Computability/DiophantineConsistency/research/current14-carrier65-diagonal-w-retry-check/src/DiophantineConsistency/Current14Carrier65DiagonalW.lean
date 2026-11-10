import DiophantineConsistency.Current14Carrier65DiagonalBinding

/-! Candidate leading coefficient for the diagonal W factor. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Current14Carrier65DiagonalW
open Sign17UnivariateDegree Current14Carrier65DiagonalBinding

def w (beta K : ℤ) : P :=
  (Polynomial.C K + Polynomial.X) *
      (Polynomial.C beta * Polynomial.X + 1 - Polynomial.X - Polynomial.X) +
    (Polynomial.C beta * Polynomial.X + 1 - Polynomial.X) -
    Polynomial.X * (Polynomial.C beta * Polynomial.X)

theorem w_formula (beta K : ℤ) :
    w beta K = Polynomial.C (-2) * Polynomial.X ^ 2 +
      Polynomial.C (K * (beta - 2) + beta) * Polynomial.X + Polynomial.C (K + 1) := by
  simp only [w, map_add, map_sub, map_mul, map_ofNat, map_one, map_neg]
  ring

theorem w_coeff_two (beta K : ℤ) : (w beta K).coeff 2 = -2 := by
  rw [w_formula]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C, if_pos rfl,
    if_neg (by decide : (2 : ℕ) ≠ 1), if_neg (by decide : (2 : ℕ) ≠ 0), add_zero]

theorem w_degree (beta K : ℤ) : (w beta K).natDegree = 2 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · rw [w_formula]
    have h2 : (Polynomial.C (-2 : ℤ) * (Polynomial.X : P) ^ 2).natDegree ≤ 2 :=
      Polynomial.natDegree_C_mul_X_pow_le (-2) 2
    have h1 : (Polynomial.C (K * (beta - 2) + beta) * (Polynomial.X : P)).natDegree ≤ 1 := by
      simpa using Polynomial.natDegree_C_mul_X_pow_le (K * (beta - 2) + beta) 1
    have h0 : (Polynomial.C (K + 1) : P).natDegree ≤ 0 :=
      le_of_eq (Polynomial.natDegree_C (K + 1))
    exact Polynomial.natDegree_add_le_of_degree_le
      (Polynomial.natDegree_add_le_of_degree_le h2 (h1.trans (by decide))) (h0.trans (by decide))
  · rw [w_coeff_two]
    decide

theorem actual_W_eq (p : Fin 4 → ℤ) : (axisCore p).W = w (p 0) (p 1) := by rfl

theorem actual_W_degree (p : Fin 4 → ℤ) : (axisCore p).W.natDegree = 2 := by
  rw [actual_W_eq]
  exact w_degree (p 0) (p 1)

end DiophantineConsistency.Current14Carrier65DiagonalW

#print axioms DiophantineConsistency.Current14Carrier65DiagonalW.w_coeff_two
#print axioms DiophantineConsistency.Current14Carrier65DiagonalW.w_degree
#print axioms DiophantineConsistency.Current14Carrier65DiagonalW.actual_W_degree
