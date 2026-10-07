import OAI.Combinatorics.Progressions.Estimates.NonprincipalDilation
import OAI.Combinatorics.Progressions.Lattices.AffineAuxiliaryVariables

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem monomialArrayPolynomial_indexed_split {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (he : Function.Injective e)
    (principal : B → K →₀ ℕ) (hp : Function.Injective principal) (hp0 : ∀ b, principal b ≠ 0)
    (index : B → C) (hindex : ∀ b, e (index b) = principal b) (a : C → ℝ) :
    monomialArrayPolynomial e a = MvPolynomial.C ((monomialArrayPolynomial e a).coeff 0) +
      (∑ b, MvPolynomial.monomial (principal b) (a (index b))) +
      ∑ j ∈ nonprincipalCoefficientSlots e principal, MvPolynomial.monomial (e j) (a j) := by
  classical
  have hS : (monomialArrayPolynomial e a).support ⊆ monomialExponentSet e := by
    intro m hm
    obtain ⟨j, rfl⟩ := monomialArrayPolynomial_support_subset e a hm
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hs := polynomial_coefficient_split_principal_on (monomialArrayPolynomial e a)
    (monomialExponentSet e) hS principal hp hp0
  rw [← nonprincipalCoefficientSlots_sum e he principal] at hs
  have hc (b) : (monomialArrayPolynomial e a).coeff (principal b) = a (index b) := by
    rw [← hindex b]
    exact monomialArrayPolynomial_coeff e he a (index b)
  simpa only [hc, monomialArrayPolynomial_coeff e he] using hs

theorem nonprincipalDilation_constant_coeff {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) (t : ℝ) (a : C → ℝ) :
    (monomialArrayPolynomial e (fun j => nonprincipalDilation e principal t j*a j)).coeff 0 =
      (monomialArrayPolynomial e a).coeff 0 := by
  classical
  simp only [monomialArrayPolynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : e j = 0
  · simp only [hj, ite_true, nonprincipalDilation_zero e principal t j hj, one_mul]
  · simp only [hj, ite_false]

theorem monomialArrayPolynomial_dilated_split {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (he : Function.Injective e)
    (principal : B → K →₀ ℕ) (hp : Function.Injective principal) (hp0 : ∀ b, principal b ≠ 0)
    (index : B → C) (hindex : ∀ b, e (index b) = principal b) (t : ℝ) (a : C → ℝ) :
    monomialArrayPolynomial e (fun j => nonprincipalDilation e principal t j*a j) =
      MvPolynomial.C ((monomialArrayPolynomial e a).coeff 0) +
      (∑ b, MvPolynomial.monomial (principal b) (a (index b))) +
      ∑ j ∈ nonprincipalCoefficientSlots e principal, MvPolynomial.monomial (e j) (t*a j) := by
  have hs := monomialArrayPolynomial_indexed_split e he principal hp hp0 index hindex
    (fun j => nonprincipalDilation e principal t j*a j)
  rw [nonprincipalDilation_constant_coeff] at hs
  have hpv (b) : nonprincipalDilation e principal t (index b)*a (index b) = a (index b) := by
    rw [nonprincipalDilation_principal e principal t (index b) b (hindex b), one_mul]
  simp_rw [hpv] at hs
  rw [hs]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [nonprincipalDilation_mem e principal t j hj]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem monomialArrayPolynomial_affine_dilated_split {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (he : Function.Injective e)
    (principal : B → K →₀ ℕ) (hp : Function.Injective principal) (hp0 : ∀ b, principal b ≠ 0)
    (index : B → C) (hindex : ∀ b, e (index b) = principal b) (t : ℝ) (c w r : C → ℝ) :
    monomialArrayPolynomial e (fun j => nonprincipalDilation e principal t j*c j +
      (nonprincipalDilation e principal t j*w j)*r j) =
      MvPolynomial.C ((monomialArrayPolynomial e (fun j => c j+w j*r j)).coeff 0) +
      (∑ b, MvPolynomial.monomial (principal b) (c (index b)+w (index b)*r (index b))) +
      ∑ j ∈ nonprincipalCoefficientSlots e principal, MvPolynomial.monomial (e j) (t*(c j+w j*r j)) := by
  have ha : (fun j => nonprincipalDilation e principal t j*c j +
      (nonprincipalDilation e principal t j*w j)*r j) =
      (fun j => nonprincipalDilation e principal t j*(c j+w j*r j)) := by
    funext j
    ring
  rw [ha]
  exact monomialArrayPolynomial_dilated_split e he principal hp hp0 index hindex t _

theorem rawProductArrayPolynomial_affine_auxiliary {D G Z : Type*}
    {B C : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (C d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (e : ∀ d, C d → SamplerTupleIndex G B h →₀ ℕ)
    (he : ∀ d, Function.Injective (e d)) (index : ∀ d, B d → C d)
    (hindex : ∀ d b, e d (index d b) = canonicalPrincipalExponent h d b)
    (t : ℝ) (c w r : ∀ d, C d → ℝ) (z : Z → ℝ) (d : D) :
    rawProductArrayPolynomial h
      (fun d => nonprincipalCoefficientSlots (e d) (canonicalPrincipalExponent h d)) e
      (fun d b v => .inr ⟨d, b, v⟩)
      (fun d b => c d (index d b)+w d (index d b)*r d (index d b))
      (fun d j => t * (affineCoefficientAllowance (c d j) (w d j) *
        affineAuxiliaryVariables c w z r (affineAuxiliaryCoefficient d j)))
      (fun d => (monomialArrayPolynomial (e d) (fun j => c d j+w d j*r d j)).coeff 0) d =
      monomialArrayPolynomial (e d) (fun j =>
        nonprincipalDilation (e d) (canonicalPrincipalExponent h d) t j*c d j +
          (nonprincipalDilation (e d) (canonicalPrincipalExponent h d) t j*w d j)*r d j) := by
  have hs := monomialArrayPolynomial_affine_dilated_split (e d) (he d)
    (canonicalPrincipalExponent h d) (canonicalPrincipalExponent_injective h d (hh d))
    (canonicalPrincipalExponent_ne_zero h d (hh d)) (index d) (hindex d) t (c d) (w d) (r d)
  simpa only [rawProductArrayPolynomial, canonicalPrincipalExponent, productBlockExponent_monomial,
    affineAuxiliaryVariables_coefficient] using hs.symm

end Erdos3

end

end OAI
