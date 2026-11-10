import DiophantineConsistency.Sign24LeadingN0

/-! SOURCE-ONLY: the eighth coefficient of the N0 square on the axis. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign24LeadingN0
open MvPolynomial

theorem n0_square_coeff :
    MvPolynomial.coeff (Finsupp.single (0 : Fin 1) 8)
      ((-(X 0)^4 - 2*(X 0)^2 - 1)^2 : MvPolynomial (Fin 1) ℤ) = 1 := by
  have h : ((-(X 0)^4 - 2*(X 0)^2 - 1)^2 : MvPolynomial (Fin 1) ℤ) =
      (X 0)^8 + C (4 : ℤ)*(X 0)^6 + C (6 : ℤ)*(X 0)^4 +
        C (4 : ℤ)*(X 0)^2 + C (1 : ℤ) := by
    simp only [map_one, map_natCast]
    ring
  rw [h]
  simp [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_single_X_pow, MvPolynomial.coeff_C]
end DiophantineConsistency.Sign24LeadingN0
#print axioms DiophantineConsistency.Sign24LeadingN0.n0_square_coeff
