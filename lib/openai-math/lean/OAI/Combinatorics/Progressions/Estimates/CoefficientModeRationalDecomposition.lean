import OAI.Combinatorics.Progressions.Polynomial.CoefficientModeDiagonalPolynomial

namespace OAI

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators Classical

theorem coefficientMode_integer_row_decomposition {I K J : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] [Fintype J] {n : ℕ}
    (frequency : (K →₀ ℕ) → J → ℤ) (a : Fin (n + 1) → K → ℤ)
    (p : VectorPolynomial I ℝ (J → ℝ)) (hp : Homogeneous (n + 1) p)
    (N s : I → ℕ) (hs : ∀ k, 0 < s k) {ζ : ℝ} (hζ : 0 < ζ)
    (hN : ∀ k, multiaffineBiasBudget n ζ ≤ N k)
    (H : I → ℝ) (hH : ∀ k, 0 < H k) {A : ℝ} (hA : 0 ≤ A)
    (hscale : ∀ k, H k ≤ A * ((s k : ℝ) * (N k : ℝ)))
    (hbias : ζ ≤ ‖𝔼 x : Fin (n + 1) → ∀ k, Fin (N k),
      𝔼 y : Fin (n + 1) → ∀ k, Fin (N k),
        character ((polynomialTopSymbol (n + 1) (coefficientModePolynomial
          (coefficientFunctional (fun d j => (frequency d j : ℝ))) p)
          (fun i z => (a i z.1 : ℝ) *
            ((s z.2 : ℝ) * ((x i z.2).val : ℝ) - (s z.2 : ℝ) * ((y i z.2).val : ℝ))) : ℝ) :
              CircleFourier.Circle)‖) :
    ∃ D : ℕ, 0 < D ∧
      (D : ℝ) ≤ ∏ j : Fin (n + 1) → I, (multiaffineBiasBudget n ζ * ∏ i, (s (j i) : ℝ)) ∧
      ∃ E : MvPolynomial I ℝ, ∃ Q : MvPolynomial I ℤ,
        integerRowPolynomial (factorialContractedRow frequency a) p =
          E + MvPolynomial.C (1 / (D : ℝ)) * MvPolynomial.map (Int.castRingHom ℝ) Q ∧
        ∀ α, |E.coeff α| ≤ (Fintype.card I : ℝ) ^ (n + 1) *
          (A ^ (n + 1) * multiaffineBiasBudget n ζ) / monomialScale H α := by
  let P := coefficientModePolynomial (coefficientFunctional (fun d j => (frequency d j : ℝ))) p
  let F := rowTopSymbolMultilinear (n + 1) P (coefficientModePolynomial_degree _ p hp)
    (fun i k => (a i k : ℝ))
  have hdiag (w : I → ℝ) :
      MvPolynomial.eval w (integerRowPolynomial (factorialContractedRow frequency a) p) =
        F (fun _ => w) := by
    simpa only [F, P, rowTopSymbolMultilinear_apply] using
      coefficientMode_diagonal_polynomial frequency a p hp w
  apply paired_multilinear_polynomial_approximation F
    (integerRowPolynomial (factorialContractedRow frequency a) p) hdiag N s hs hζ hN H hH hA hscale
  simpa only [F, P, rowTopSymbolMultilinear_apply] using hbias

end Erdos3.VectorPolynomial

end

end OAI
