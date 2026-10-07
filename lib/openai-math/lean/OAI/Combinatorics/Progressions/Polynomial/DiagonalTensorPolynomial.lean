import OAI.Combinatorics.Progressions.Estimates.PrincipalBlockExponent
import OAI.Combinatorics.Progressions.Geometry.MultilinearCoordinateExpansion

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def tensorDiagonalPolynomial {I R : Type*} [Fintype I] [CommSemiring R]
    {h : ℕ} (θ : (Fin h → I) → R) : MvPolynomial I R :=
  ∑ j : Fin h → I, MvPolynomial.C (θ j) * ∏ i, MvPolynomial.X (j i)

theorem tensorDiagonalPolynomial_eval {I R : Type*} [Fintype I] [CommSemiring R]
    {h : ℕ} (θ : (Fin h → I) → R) (w : I → R) :
    MvPolynomial.eval w (tensorDiagonalPolynomial θ) = ∑ j, θ j * ∏ i, w (j i) := by
  simp [tensorDiagonalPolynomial]

theorem tensorDiagonalPolynomial_add {I R : Type*} [Fintype I] [CommSemiring R]
    {h : ℕ} (θ ψ : (Fin h → I) → R) :
    tensorDiagonalPolynomial (fun j => θ j + ψ j) =
      tensorDiagonalPolynomial θ + tensorDiagonalPolynomial ψ := by
  simp [tensorDiagonalPolynomial, add_mul, Finset.sum_add_distrib]

theorem tensorDiagonalPolynomial_mul {I R : Type*} [Fintype I] [CommSemiring R]
    {h : ℕ} (c : R) (θ : (Fin h → I) → R) :
    tensorDiagonalPolynomial (fun j => c * θ j) = MvPolynomial.C c * tensorDiagonalPolynomial θ := by
  simp [tensorDiagonalPolynomial, Finset.mul_sum, mul_assoc]

theorem tensorDiagonalPolynomial_map {I R S : Type*} [Fintype I]
    [CommSemiring R] [CommSemiring S] {h : ℕ} (f : R →+* S) (θ : (Fin h → I) → R) :
    MvPolynomial.map f (tensorDiagonalPolynomial θ) = tensorDiagonalPolynomial (fun j => f (θ j)) := by
  simp [tensorDiagonalPolynomial]

theorem tensorDiagonalPolynomial_eq_sum_monomial {I : Type*} [Fintype I]
    {h : ℕ} (θ : (Fin h → I) → ℝ) :
    tensorDiagonalPolynomial θ = ∑ j, MvPolynomial.monomial (productBlockExponent j) (θ j) := by
  simp only [tensorDiagonalPolynomial, productBlockExponent_monomial]

theorem tensorDiagonalPolynomial_multilinear_eval {I R : Type*} [Fintype I]
    [DecidableEq I] [CommRing R] {h : ℕ}
    (F : MultilinearMap R (fun _ : Fin h => I → R) R) (w : I → R) :
    MvPolynomial.eval w
      (tensorDiagonalPolynomial (fun j => F (fun i => Pi.single (j i) (1 : R)))) = F (fun _ => w) := by
  rw [tensorDiagonalPolynomial_eval]
  exact (multilinear_diagonal_expansion F w).symm

end Erdos3

end

end OAI
