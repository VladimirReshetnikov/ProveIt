import DiophantineConsistency.Sign23LeadingRows

/-! SOURCE-ONLY: eighth coefficients of the two quartic axis squares. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign23LeadingRows
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

theorem dc2_square_coeff :
    MvPolynomial.coeff (Finsupp.single (0 : Fin 1) 8)
      ((-(X 0)^4 - 6*(X 0)^3 - 12*(X 0)^2 - 10*(X 0) - 3)^2 : MvPolynomial (Fin 1) ℤ) = 1 := by
  have h : ((-(X 0)^4 - 6*(X 0)^3 - 12*(X 0)^2 - 10*(X 0) - 3)^2 : MvPolynomial (Fin 1) ℤ) =
      (X 0)^8 + (12 : ℕ) • (X 0)^7 + (60 : ℕ) • (X 0)^6 +
      (164 : ℕ) • (X 0)^5 + (270 : ℕ) • (X 0)^4 + (276 : ℕ) • (X 0)^3 +
      (172 : ℕ) • (X 0)^2 + (60 : ℕ) • (X 0) + (9 : ℕ) • 1 := by
    simp only [nsmul_eq_mul]
    ring
  have hn : (0 : Fin 1 →₀ ℕ) ≠ Finsupp.single 0 8 := by
    intro he
    have hh := congrArg (fun f : Fin 1 →₀ ℕ => f 0) he
    norm_num at hh
  rw [h]
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_smul,
    MvPolynomial.coeff_single_X_pow, MvPolynomial.coeff_one, MvPolynomial.coeff_X]
  norm_num [hn]
end DiophantineConsistency.Sign23LeadingRows
#print axioms DiophantineConsistency.Sign23LeadingRows.n0_square_coeff
#print axioms DiophantineConsistency.Sign23LeadingRows.dc2_square_coeff
