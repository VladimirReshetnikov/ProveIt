import OAI.Combinatorics.Progressions.Polynomial.WeightedLinearPolynomialRestriction

namespace OAI

section

namespace Erdos3

variable {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq τ]

theorem polynomialLinearRestriction_denominator_pos
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (P : MvPolynomial σ ℚ) (d : ℕ) :
    0 < polynomialDenominator P *
      matrixDenominator (fun i j => A (Pi.single j 1) i) ^ d :=
  Nat.mul_pos (polynomialDenominator_pos P)
    (pow_pos (matrixDenominator_pos _) _)

theorem polynomialLinearRestriction_denominator_le
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (P : MvPolynomial σ ℚ) {d K H : ℕ}
    (hd : P.totalDegree ≤ d) (hP : RationalPolynomialHeightLE P K)
    (hA : ∀ i j, RationalHeightLE (A (Pi.single j 1) i) H) :
    polynomialDenominator P * matrixDenominator (fun i j => A (Pi.single j 1) i) ^ d ≤
      K ^ ((Fintype.card σ + 1) ^ d) * H ^ ((Fintype.card σ * Fintype.card τ) * d) := by
  have hcard : P.support.card ≤ (Fintype.card σ + 1) ^ d :=
    boundedExponentSet_card_le P.support d
      (fun _ hm => (MvPolynomial.le_totalDegree hm).trans hd)
  have hpoly : polynomialDenominator P ≤ K ^ ((Fintype.card σ + 1) ^ d) :=
    (polynomialDenominator_le P hP).trans (Nat.pow_le_pow_right hP.one_le hcard)
  have hmatrix := Nat.pow_le_pow_left
    (matrixDenominator_le (fun i j => A (Pi.single j 1) i) hA) d
  rw [← pow_mul] at hmatrix
  exact Nat.mul_le_mul hpoly hmatrix

theorem polynomialLinearRestriction_denominator_bounds
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (P : MvPolynomial σ ℚ) {d K H : ℕ}
    (hd : P.totalDegree ≤ d) (hP : RationalPolynomialHeightLE P K)
    (hA : ∀ i j, RationalHeightLE (A (Pi.single j 1) i) H) :
    0 < polynomialDenominator P * matrixDenominator (fun i j => A (Pi.single j 1) i) ^ d ∧
      polynomialDenominator P * matrixDenominator (fun i j => A (Pi.single j 1) i) ^ d ≤
        K ^ ((Fintype.card σ + 1) ^ d) * H ^ ((Fintype.card σ * Fintype.card τ) * d) :=
  ⟨polynomialLinearRestriction_denominator_pos A P d,
    polynomialLinearRestriction_denominator_le A P hd hP hA⟩

end Erdos3

end

end OAI
