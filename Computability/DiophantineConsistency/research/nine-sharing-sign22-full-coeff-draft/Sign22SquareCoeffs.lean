import DiophantineConsistency.Sign22LeadingRows

/-! SOURCE-ONLY: twelfth coefficients of the two sextic axis squares. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign22LeadingRows
open MvPolynomial

theorem dc2_square_coeff :
    MvPolynomial.coeff (Finsupp.single (0 : Fin 1) 12)
      ((-(4*(X 0)^2 + 8*(X 0) + 3) * (2*(X 0)^2 + 3*(X 0) + 1)^2)^2 : MvPolynomial (Fin 1) ℤ) = 256 := by
  have h : ((-(4*(X 0)^2 + 8*(X 0) + 3) * (2*(X 0)^2 + 3*(X 0) + 1)^2)^2 : MvPolynomial (Fin 1) ℤ) =
      (256 : ℕ) • (X 0)^12 +
        (2560 : ℕ) • (X 0)^11 +
        (11520 : ℕ) • (X 0)^10 +
        (30848 : ℕ) • (X 0)^9 +
        (54752 : ℕ) • (X 0)^8 +
        (67872 : ℕ) • (X 0)^7 +
        (60272 : ℕ) • (X 0)^6 +
        (38648 : ℕ) • (X 0)^5 +
        (17769 : ℕ) • (X 0)^4 +
        (5716 : ℕ) • (X 0)^3 +
        (1222 : ℕ) • (X 0)^2 +
        (156 : ℕ) • (X 0) +
        (9 : ℕ) • 1 := by
    simp only [nsmul_eq_mul]
    ring
  have hn : (0 : Fin 1 →₀ ℕ) ≠ Finsupp.single 0 12 := by
    intro he
    have hh := congrArg (fun f : Fin 1 →₀ ℕ => f 0) he
    norm_num at hh
  rw [h]
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_smul,
    MvPolynomial.coeff_single_X_pow, MvPolynomial.coeff_one, MvPolynomial.coeff_X]
  norm_num [hn]

theorem n0_square_coeff :
    MvPolynomial.coeff (Finsupp.single (0 : Fin 1) 12)
      ((-4*(X 0)^6 - 8*(X 0)^5 - 8*(X 0)^4 - 8*(X 0)^3 - 4*(X 0)^2 - 1)^2 : MvPolynomial (Fin 1) ℤ) = 16 := by
  have h : ((-4*(X 0)^6 - 8*(X 0)^5 - 8*(X 0)^4 - 8*(X 0)^3 - 4*(X 0)^2 - 1)^2 : MvPolynomial (Fin 1) ℤ) =
      (16 : ℕ) • (X 0)^12 +
        (64 : ℕ) • (X 0)^11 +
        (128 : ℕ) • (X 0)^10 +
        (192 : ℕ) • (X 0)^9 +
        (224 : ℕ) • (X 0)^8 +
        (192 : ℕ) • (X 0)^7 +
        (136 : ℕ) • (X 0)^6 +
        (80 : ℕ) • (X 0)^5 +
        (32 : ℕ) • (X 0)^4 +
        (16 : ℕ) • (X 0)^3 +
        (8 : ℕ) • (X 0)^2 +
        1 := by
    simp only [nsmul_eq_mul]
    ring
  have hn : (0 : Fin 1 →₀ ℕ) ≠ Finsupp.single 0 12 := by
    intro he
    have hh := congrArg (fun f : Fin 1 →₀ ℕ => f 0) he
    norm_num at hh
  rw [h]
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_smul,
    MvPolynomial.coeff_single_X_pow, MvPolynomial.coeff_one, MvPolynomial.coeff_X]
  norm_num [hn]
end DiophantineConsistency.Sign22LeadingRows
#print axioms DiophantineConsistency.Sign22LeadingRows.dc2_square_coeff
#print axioms DiophantineConsistency.Sign22LeadingRows.n0_square_coeff
