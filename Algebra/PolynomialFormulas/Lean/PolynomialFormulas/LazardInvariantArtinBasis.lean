import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# The Artin monomials for the symmetric-polynomial extension

This file records the finite, graded family that occurs in Lazard's
Gröbner-basis proof.  For `n` variables its exponents satisfy

`a i < n - i`.

Consequently there are `n!` such monomials and every one has total degree at
most `n * (n - 1) / 2`.  These statements are independent of the coefficient
ring.  The module-basis theorem is developed below this combinatorial layer;
none of the declarations in this file assumes freeness or projectivity.
-/

namespace LeanProofs.PolynomialFormulas.LazardInvariantArtinBasis

open scoped BigOperators
open Finset MvPolynomial

set_option autoImplicit false

noncomputable section

/-- The exponent choices for the standard monomials of Lazard's triangular
Gröbner basis.  The variable `i` may occur with exponents
`0, ..., n - i - 1`. -/
abbrev ArtinIndex (n : ℕ) := ∀ i : Fin n, Fin (n - i.1)

/-- The exponent vector underlying an Artin index. -/
def artinExponent {n : ℕ} (a : ArtinIndex n) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (a i).1

@[simp]
theorem artinExponent_apply {n : ℕ} (a : ArtinIndex n) (i : Fin n) :
    artinExponent a i = (a i).1 := by
  simp [artinExponent]

/-- The total degree of the Artin monomial indexed by `a`. -/
def artinDegree {n : ℕ} (a : ArtinIndex n) : ℕ :=
  ∑ i : Fin n, (a i).1

theorem artinExponent_degree {n : ℕ} (a : ArtinIndex n) :
    (artinExponent a).degree = artinDegree a := by
  rw [Finsupp.degree_eq_sum]
  simp [artinDegree, artinExponent]

/-- Every standard exponent is pointwise bounded by the corresponding
staircase exponent. -/
theorem artinExponent_le_staircase {n : ℕ} (a : ArtinIndex n) (i : Fin n) :
    (a i).1 ≤ n - 1 - i.1 := by
  have hlt : (a i).1 < n - i.1 := (a i).2
  omega

/-- Lazard's uniform degree bound for the standard monomials. -/
theorem artinDegree_le {n : ℕ} (a : ArtinIndex n) :
    artinDegree a ≤ n * (n - 1) / 2 := by
  calc
    artinDegree a ≤ ∑ i : Fin n, (n - 1 - i.1) :=
      Finset.sum_le_sum fun i _ => artinExponent_le_staircase a i
    _ = ∑ i ∈ Finset.range n, (n - 1 - i) :=
      Fin.sum_univ_eq_sum_range (fun i => n - 1 - i) n
    _ = ∑ i ∈ Finset.range n, i := Finset.sum_range_reflect (fun i => i) n
    _ = n * (n - 1) / 2 := Finset.sum_range_id n

/-- The standard Artin monomial in `n` variables. -/
def artinMonomial (R : Type*) [CommSemiring R] {n : ℕ} (a : ArtinIndex n) :
    MvPolynomial (Fin n) R :=
  monomial (artinExponent a) 1

theorem artinMonomial_isHomogeneous (R : Type*) [CommSemiring R]
    {n : ℕ} (a : ArtinIndex n) :
    IsHomogeneous (artinMonomial R a) (artinDegree a) := by
  exact isHomogeneous_monomial 1 (artinExponent_degree a)

theorem totalDegree_artinMonomial (R : Type*) [CommSemiring R] [Nontrivial R]
    {n : ℕ} (a : ArtinIndex n) :
    (artinMonomial R a).totalDegree = artinDegree a := by
  rw [artinMonomial, totalDegree_monomial _ one_ne_zero]
  exact artinExponent_degree a

theorem totalDegree_artinMonomial_le (R : Type*) [CommSemiring R]
    {n : ℕ} (a : ArtinIndex n) :
    (artinMonomial R a).totalDegree ≤ n * (n - 1) / 2 :=
  (totalDegree_monomial_le _ _).trans <|
    (artinExponent_degree a).le.trans (artinDegree_le a)

/-- Reversing the staircase turns its factor sizes into `1, ..., n`. -/
theorem prod_staircase (n : ℕ) :
    (∏ i : Fin n, (n - i.1)) = n.factorial := by
  calc
    (∏ i : Fin n, (n - i.1)) = ∏ i ∈ Finset.range n, (n - i) :=
      Fin.prod_univ_eq_prod_range _ _
    _ = ∏ i ∈ Finset.range n, (n - 1 - i + 1) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hi' : i < n := Finset.mem_range.mp hi
      omega
    _ = ∏ i ∈ Finset.range n, (i + 1) :=
      Finset.prod_range_reflect (fun i => i + 1) n
    _ = n.factorial := Finset.prod_range_add_one_eq_factorial n

/-- There are exactly `n!` standard Artin monomials. -/
theorem card_artinIndex (n : ℕ) : Fintype.card (ArtinIndex n) = n.factorial := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  exact prod_staircase n

end

end LeanProofs.PolynomialFormulas.LazardInvariantArtinBasis
