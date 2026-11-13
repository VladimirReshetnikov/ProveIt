import DiophantineConsistency.Sign21LeadingRow

/-! SOURCE-ONLY: fourteenth coefficient of the septic axis square. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign21LeadingRow
open MvPolynomial

theorem leading_square_coeff :
    MvPolynomial.coeff (Finsupp.single (0 : Fin 1) 14)
      ((-(X 0)^7 - 6*(X 0)^6 - 13*(X 0)^5 - 12*(X 0)^4 - 4*(X 0)^3)^2 : MvPolynomial (Fin 1) ℤ) = 1 := by
  have h : ((-(X 0)^7 - 6*(X 0)^6 - 13*(X 0)^5 - 12*(X 0)^4 - 4*(X 0)^3)^2 : MvPolynomial (Fin 1) ℤ) =
      (X 0)^14 + (12 : ℕ) • (X 0)^13 + (62 : ℕ) • (X 0)^12 +
        (180 : ℕ) • (X 0)^11 + (321 : ℕ) • (X 0)^10 + (360 : ℕ) • (X 0)^9 +
        (248 : ℕ) • (X 0)^8 + (96 : ℕ) • (X 0)^7 + (16 : ℕ) • (X 0)^6 := by
    simp only [nsmul_eq_mul]
    ring
  rw [h]
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_smul,
    MvPolynomial.coeff_single_X_pow]
  norm_num
end DiophantineConsistency.Sign21LeadingRow
#print axioms DiophantineConsistency.Sign21LeadingRow.leading_square_coeff
