import DiophantineConsistency.Current14Carrier65DiagonalBase

/-! Candidate univariate core-factor degrees; actual Carrier65 binding is separate. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Current14Carrier65DiagonalCore
open Sign17UnivariateDegree Sign17AxisDegreeRoot Current14Carrier65DiagonalBase

abbrev twice : P := Polynomial.C 2 * Polynomial.X
abbrev c (beta : ℤ) : P := twice * y beta + Polynomial.X
abbrev a (beta : ℤ) : P := e beta + y beta
abbrev H (beta : ℤ) : P := Polynomial.C 4 * a beta + 3
abbrev delta (beta : ℤ) : P := a beta ^ 2 + H beta

theorem twice_degree : twice.natDegree = 1 := by
  change (Polynomial.C (2 : ℤ) * (Polynomial.X : P)).natDegree = 1
  rw [product_degree _ _ (Polynomial.C_ne_zero.mpr (by decide)) (by simp)]
  simp

theorem c_degree (beta : ℤ) (hbeta : beta ≠ 0) : (c beta).natDegree = 5 := by
  have h : (twice * y beta).natDegree = 5 := by
    simpa using degree_product twice (y beta) 1 4 twice_degree (y_degree beta hbeta)
      (by decide) (by decide)
  exact degree_sum _ _ 5 1 h Polynomial.natDegree_X (by decide)

theorem a_degree (beta : ℤ) (hbeta : beta ≠ 0) : (a beta).natDegree = 6 := by
  exact degree_sum _ _ 6 4 (e_degree beta hbeta) (y_degree beta hbeta) (by decide)

theorem H_degree (beta : ℤ) (hbeta : beta ≠ 0) : (H beta).natDegree = 6 := by
  have ha := a_degree beta hbeta
  have hm : (Polynomial.C (4 : ℤ) * a beta).natDegree = 6 := by
    rw [product_degree _ _ (Polynomial.C_ne_zero.mpr (by decide))
      (ne_zero_of_positive_degree _ _ ha (by decide)), ha]
    simp
  exact degree_sum _ _ 6 0 hm (by simp) (by decide)

theorem delta_degree (beta : ℤ) (hbeta : beta ≠ 0) : (delta beta).natDegree = 12 := by
  have ha := a_degree beta hbeta
  have h2 : (a beta ^ 2).natDegree = 12 := by
    simpa [pow_two] using degree_product (a beta) (a beta) 6 6 ha ha (by decide) (by decide)
  exact degree_sum _ _ 12 6 h2 (H_degree beta hbeta) (by decide)

end DiophantineConsistency.Current14Carrier65DiagonalCore

#print axioms DiophantineConsistency.Current14Carrier65DiagonalCore.c_degree
#print axioms DiophantineConsistency.Current14Carrier65DiagonalCore.a_degree
#print axioms DiophantineConsistency.Current14Carrier65DiagonalCore.H_degree
#print axioms DiophantineConsistency.Current14Carrier65DiagonalCore.delta_degree
