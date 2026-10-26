import DiophantineConsistency.SidonPositions
import DiophantineConsistency.QuadraticFiber
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Fintype.Prod

/-!
# Coefficient extraction for an explicit quadratic Sidon encoding

The cubic-size positions distinguish unordered products of coordinates.
Squaring the coordinate encoding therefore has coefficient `u_i^2` on a
diagonal position and `2*u_i*u_j` off the diagonal. A complementary exponent
encoding extracts twice any supplied quadratic form. These are coefficient
identities, without a claim that they replace the complete Jones reduction.
-/

namespace DiophantineConsistency.QuadraticCoding

open Polynomial SidonPositions
open scoped BigOperators

variable {R : Type*} [CommRing R] {m : ℕ}

/-- A finite coordinate encoding; coordinate zero can be set to one when
constant and linear terms are included in a quadratic form. -/
noncomputable def encoded (u : Fin (m + 1) → R) : R[X] :=
  ∑ i, monomial (weight m i) (u i)

theorem encoded_eq_sum (u : Fin (m + 1) → R) :
    encoded u = ∑ i, C (u i) * X ^ weight m i := by
  simp only [encoded, C_mul_X_pow_eq_monomial]

/-- The literal ordered double sum before equal positions are collected. -/
theorem encoded_square (u : Fin (m + 1) → R) :
    encoded u ^ 2 = ∑ i, ∑ j, monomial (weight m i + weight m j) (u i * u j) := by
  simp only [pow_two, encoded, Finset.sum_mul, Finset.mul_sum, monomial_mul_monomial]
  rw [Finset.sum_comm]

theorem coeff_encoded_square_diagonal (u : Fin (m + 1) → R) (i : Fin (m + 1)) :
    (encoded u ^ 2).coeff (weight m i + weight m i) = u i ^ 2 := by
  simpa [encoded] using
    QuadraticFiber.coeff_square_at_isolated (weight m) u i i
      (fun a b => weight_sum_eq_iff a b i i)

theorem coeff_encoded_square_offDiagonal (u : Fin (m + 1) → R)
    (i j : Fin (m + 1)) (hij : i ≠ j) :
    (encoded u ^ 2).coeff (weight m i + weight m j) = 2 * u i * u j := by
  simpa only [encoded, if_neg hij] using
    QuadraticFiber.coeff_square_at_isolated (weight m) u i j
      (fun a b => weight_sum_eq_iff a b i j)

/-- The coefficient statement on the supplied canonical unordered-pair domain. -/
theorem coeff_encoded_square (u : Fin (m + 1) → R) (p : PairIndex m) :
    (encoded u ^ 2).coeff (pairWeight p) =
      if p.val.1 = p.val.2 then u p.val.1 ^ 2 else 2 * u p.val.1 * u p.val.2 := by
  exact QuadraticFiber.coeff_square_at_isolated (weight m) u p.val.1 p.val.2
    (fun a b => weight_sum_eq_iff a b p.val.1 p.val.2)

/-- Supplied coefficients of a quadratic form, with constant and linear terms
available by assigning coordinate zero the value one. -/
def quadraticValue (a : PairIndex m → R) (u : Fin (m + 1) → R) : R :=
  ∑ p, a p * u p.val.1 * u p.val.2

/-- Diagonal coefficients receive the factor lost when an ordered square is
collected into unordered pairs. -/
def correction (p : PairIndex m) : R := if p.val.1 = p.val.2 then 2 else 1

/-- Complementary exponents bring every selected quadratic term to `L`. -/
noncomputable def complementary (a : PairIndex m → R) (L : ℕ) : R[X] :=
  ∑ p, monomial (L - pairWeight p) (correction p * a p)

/-- The explicit Sidon encoding extracts twice the supplied quadratic value. -/
theorem coeff_square_mul_complementary (a : PairIndex m → R)
    (u : Fin (m + 1) → R) (L : ℕ) (hL : ∀ p : PairIndex m, pairWeight p ≤ L) :
    (encoded u ^ 2 * complementary a L).coeff L = 2 * quadraticValue a u := by
  classical
  simp only [complementary, Finset.mul_sum, finsetSum_coeff]
  rw [quadraticValue, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  have hc := coeff_mul_monomial (encoded u ^ 2) (L - pairWeight p)
    (pairWeight p) (correction p * a p)
  rw [Nat.add_sub_of_le (hL p)] at hc
  rw [hc, coeff_encoded_square]
  by_cases h : p.val.1 = p.val.2
  · simp only [correction, if_pos h]
    rw [h]
    ring
  · simp only [correction, if_neg h, one_mul]
    ring

/-- A cubic choice of the coefficient position works for every supplied form. -/
def coefficientPosition (m : ℕ) : ℕ := 4 * m ^ 3 + 2 * m ^ 2 + 2 * m

theorem coeff_square_mul_complementary_cubic (a : PairIndex m → R)
    (u : Fin (m + 1) → R) :
    (encoded u ^ 2 * complementary a (coefficientPosition m)).coeff
      (coefficientPosition m) = 2 * quadraticValue a u :=
  coeff_square_mul_complementary a u _ pairWeight_le

end DiophantineConsistency.QuadraticCoding
