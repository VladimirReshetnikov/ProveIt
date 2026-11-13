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
      (X 0)^8 + (4 : ℕ) • (X 0)^6 + (6 : ℕ) • (X 0)^4 +
        (4 : ℕ) • (X 0)^2 + 1 := by
    simp only [nsmul_eq_mul]
    ring
  have hn : (0 : Fin 1 →₀ ℕ) ≠ Finsupp.single 0 8 := by
    intro he
    have hh := congrArg (fun f : Fin 1 →₀ ℕ => f 0) he
    norm_num at hh
  rw [h]
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_smul,
    MvPolynomial.coeff_single_X_pow, MvPolynomial.coeff_one]
  norm_num [hn]
end DiophantineConsistency.Sign24LeadingN0
#print axioms DiophantineConsistency.Sign24LeadingN0.n0_square_coeff
