import OAI.Combinatorics.Progressions.Estimates.PairedDiagonalApproximation

namespace OAI

section

namespace Erdos3

def PolynomialRationalApproximation {I : Type*} (T : I → ℝ) (R : ℝ)
    (P : MvPolynomial I ℝ) : Prop :=
  ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ R ∧ ∃ Q : MvPolynomial I ℤ,
    ∀ α, |P.coeff α - ((Q.coeff α : ℤ) : ℝ) / D| ≤ R / monomialScale T α

theorem polynomialRationalApproximation_of_decomposition {I : Type*}
    (T : I → ℝ) (R : ℝ) (P E : MvPolynomial I ℝ) (Q : MvPolynomial I ℤ)
    (D : ℕ) (hD : 0 < D) (hDR : (D : ℝ) ≤ R)
    (hP : P = E + MvPolynomial.C (1 / (D : ℝ)) * MvPolynomial.map (Int.castRingHom ℝ) Q)
    (hE : ∀ α, |E.coeff α| ≤ R / monomialScale T α) :
    PolynomialRationalApproximation T R P := by
  refine ⟨D, hD, hDR, Q, ?_⟩
  intro α
  rw [hP, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    integerPolynomialQuotient_coeff, add_sub_cancel_right]
  exact hE α

theorem polynomialRationalApproximation_decomposition {I : Type*}
    (T : I → ℝ) (R : ℝ) (P : MvPolynomial I ℝ)
    (h : PolynomialRationalApproximation T R P) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ R ∧
      ∃ E : MvPolynomial I ℝ, ∃ Q : MvPolynomial I ℤ,
        P = E + MvPolynomial.C (1 / (D : ℝ)) * MvPolynomial.map (Int.castRingHom ℝ) Q ∧
        ∀ α, |E.coeff α| ≤ R / monomialScale T α := by
  obtain ⟨D, hD, hDR, Q, hQ⟩ := h
  refine ⟨D, hD, hDR,
    P - MvPolynomial.C (1 / (D : ℝ)) * MvPolynomial.map (Int.castRingHom ℝ) Q, Q, ?_, ?_⟩
  · exact (sub_add_cancel P _).symm
  · intro α
    simpa only [MvPolynomial.coeff_sub, integerPolynomialQuotient_coeff] using hQ α

end Erdos3

end

section

namespace Erdos3

theorem PolynomialRationalApproximation.mono {I : Type*}
    {T : I → ℝ} {R S : ℝ} {P : MvPolynomial I ℝ}
    (h : PolynomialRationalApproximation T R P) (hRS : R ≤ S)
    (hT : ∀ i, 0 < T i) : PolynomialRationalApproximation T S P := by
  obtain ⟨D, hD, hDR, Q, hQ⟩ := h
  exact ⟨D, hD, hDR.trans hRS, Q, fun α =>
    (hQ α).trans (div_le_div_of_nonneg_right hRS (monomialScale_pos T hT α).le)⟩

end Erdos3

end

end OAI
