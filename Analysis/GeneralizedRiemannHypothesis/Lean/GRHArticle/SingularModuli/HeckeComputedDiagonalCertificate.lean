import GRHArticle.SingularModuli.HeckeDiagonalCoefficientComputation

/-!
# Connecting a finite computation with an integer Hecke diagonal
-/

namespace GRHArticle.SingularModuli

theorem natDegree_coefficientListPolynomial_le {l : List ℤ} {n : ℕ}
    (h : l.length ≤ n+1) : (coefficientListPolynomial l).natDegree ≤ n := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  have hlen : l.length ≤ i := h.trans (Nat.succ_le_of_lt hi)
  simp only [coeff_coefficientListPolynomial, List.getD_eq_getElem?_getD,
    List.getElem?_eq_none_iff.mpr hlen, Option.getD_none]

theorem coefficientListPolynomial_multiplyPackedIntegerPolynomial
    (N : ℕ) (l r : List ℤ)
    (h : (coefficientListPolynomial l * coefficientListPolynomial r).natDegree < N) :
    coefficientListPolynomial (multiplyPackedIntegerPolynomial N l r) =
      coefficientListPolynomial l * coefficientListPolynomial r := by
  ext k
  rw [coeff_coefficientListPolynomial]
  by_cases hk : k < N
  · exact getD_multiplyPackedIntegerPolynomial N l r ⟨k, hk⟩
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (h.trans_le (Nat.le_of_not_gt hk))]
    have hn : (multiplyPackedIntegerPolynomial N l r).length ≤ k := by
      rw [length_multiplyPackedIntegerPolynomial]
      exact Nat.le_of_not_gt hk
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr hn, Option.getD_none]

/-- A comparison of the two explicitly computed lists certifies the
analytic diagonal, after the degree has been bounded by the list length. -/
theorem primeHeckeDiagonalEval_eq_of_computation (p : ℕ+) [Fact (Nat.Prime (p : ℕ))]
    (cs : List ℤ) (hcs : cs.length ≤ 2*(p : ℕ)+1)
    (hcompute : computedScaledDiagonalPrefix p = computedScaledClearedPrefix p cs) :
    ∀ z : UpperHalfPlane,
      Polynomial.aeval (modularInvariant z) (coefficientListPolynomial cs) =
        -analyticPrimeHeckeDiagonal p z := by
  apply primeHeckeDiagonalEval_eq_of_integerCertificate p _
    (natDegree_coefficientListPolynomial_le hcs)
  intro k hk
  have h₁ := computedScaledDiagonalPrefix_spec p ⟨k, Nat.lt_succ_of_le hk⟩
  have h₂ := computedScaledClearedPrefix_spec p cs ⟨k, Nat.lt_succ_of_le hk⟩
  rw [hcompute] at h₁
  rw [PowerSeries.coeff_C_mul] at h₂
  exact h₁.symm.trans h₂

end GRHArticle.SingularModuli
