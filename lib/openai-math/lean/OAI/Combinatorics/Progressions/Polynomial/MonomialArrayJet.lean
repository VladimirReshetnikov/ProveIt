/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.CoefficientNormalization
import OAI.Combinatorics.Progressions.Polynomial.VectorPolynomialReconstruction

namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

noncomputable def monomialArrayPolynomial {J K : Type*} [Fintype J]
    (e : J → K →₀ ℕ) (a : J → ℝ) : MvPolynomial K ℝ :=
  ∑ j, MvPolynomial.monomial (e j) (a j)

theorem monomialArrayPolynomial_eval {J K : Type*} [Fintype J]
    (e : J → K →₀ ℕ) (a : J → ℝ) (x : K → ℝ) :
    MvPolynomial.eval x (monomialArrayPolynomial e a) =
      ∑ j, a j*∏ k ∈ (e j).support, x k^e j k := by
  simp only [monomialArrayPolynomial, map_sum, MvPolynomial.eval_monomial, Finsupp.prod]

theorem monomialArrayPolynomial_coeff {J K : Type*} [Fintype J]
    (e : J → K →₀ ℕ) (he : Function.Injective e) (a : J → ℝ) (j : J) :
    (monomialArrayPolynomial e a).coeff (e j) = a j := by
  classical
  simp only [monomialArrayPolynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
    he.eq_iff]
  simp

theorem monomialArrayPolynomial_coeff_zero_of_not_mem {J K : Type*} [Fintype J]
    (e : J → K →₀ ℕ) (a : J → ℝ) (m : K →₀ ℕ) (hm : ∀ j, e j ≠ m) :
    (monomialArrayPolynomial e a).coeff m = 0 := by
  classical
  simp only [monomialArrayPolynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  exact Finset.sum_eq_zero (fun j _ => ite_eq_right (hm j))

theorem realJetMatrix_monomialArray {α K O J : Type*} [DecidableEq α] [Fintype J]
    (e : J → K →₀ ℕ) (vertices : Finset α → K → ℝ) (rows : O → Finset α)
    (a : J → ℝ) (o : O) :
    (realJetMatrix (fun j => MvPolynomial.monomial (e j) 1) vertices rows *ᵥ a) o =
      booleanCoefficient (fun t => MvPolynomial.eval (vertices t) (monomialArrayPolynomial e a)) (rows o) := by
  rw [realJetMatrix_apply_coefficients]
  simp only [MvPolynomial.C_mul_monomial, mul_one, monomialArrayPolynomial]

theorem monomialArrayPolynomial_rescale {J K : Type*} [Fintype J]
    (e : J → K →₀ ℕ) (a : J → ℝ) (scale x : K → ℝ) (H : ℝ)
    (hH : H ≠ 0) (hscale : ∀ k, scale k ≠ 0) :
    MvPolynomial.eval (fun k => scale k*x k)
      (monomialArrayPolynomial e (fun j => H*a j/monomialScale scale (e j)))/H =
      MvPolynomial.eval x (monomialArrayPolynomial e a) := by
  rw [monomialArrayPolynomial_eval, monomialArrayPolynomial_eval, Finset.sum_div]
  exact Finset.sum_congr rfl (fun j _ => normalizedMonomialTerm (e j) scale x H (a j) hH hscale)

theorem monomialArrayPolynomial_jet_rescale {J K α : Type*} [Fintype J] [DecidableEq α]
    (e : J → K →₀ ℕ) (a : J → ℝ) (scale : K → ℝ) (vertices : Finset α → K → ℝ)
    (H : ℝ) (hH : H ≠ 0) (hscale : ∀ k, scale k ≠ 0) (s : Finset α) :
    booleanCoefficient (fun t => MvPolynomial.eval (fun k => scale k*vertices t k)
      (monomialArrayPolynomial e (fun j => H*a j/monomialScale scale (e j)))) s/H =
      booleanCoefficient (fun t => MvPolynomial.eval (vertices t) (monomialArrayPolynomial e a)) s := by
  rw [← booleanCoefficient_div]
  simp_rw [monomialArrayPolynomial_rescale e a scale _ H hH hscale]

end Erdos3

end

end OAI
