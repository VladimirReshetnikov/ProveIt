import FabiusFunction.FiniteMomentGram
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Fraction-free Gram--Stieltjes orthogonal polynomials

This module constructs the finite Gram--Stieltjes polynomial attached to an
arbitrary scalar moment sequence.  The construction is fraction-free: its
coefficient vector is the last column of the adjugate of the order-`n+1`
Hankel matrix.  The identity `H * adjugate H = det H` then proves at once that

* all pairings with `1, X, ..., X^(n-1)` vanish;
* the pairing with `X^n` is the order-`n+1` Hankel determinant; and
* the coefficient in degree `n` is the order-`n` Hankel determinant.

Over a field, if the order-`n` Hankel determinant is nonzero, division by it
gives the unique monic polynomial of degree `n` orthogonal to all lower-degree
polynomials.  Its self-pairing is the quotient of consecutive Hankel
determinants.

Everything is finite algebra.  No positivity, location or simplicity of
roots, quadrature rule, infinite continued fraction, or convergence theorem
is asserted.
-/

set_option autoImplicit false

open Finset Polynomial
open scoped BigOperators

namespace Fabius

noncomputable section

/-! ## The fraction-free adjugate construction -/

/-- The fraction-free Gram--Stieltjes numerator of order `n`.  Its coefficient
vector is the last column of the adjugate of the order-`n+1` Hankel matrix. -/
def gramStieltjesNumerator {R : Type*} [CommRing R]
    (moment : ℕ → R) (n : ℕ) : R[X] := by
  classical
  exact Polynomial.ofFn (n + 1) fun j ↦
    (momentHankelMatrix moment (n + 1)).adjugate j (Fin.last n)

/-- Coefficients below and including degree `n` are the entries of the last
adjugate column. -/
theorem gramStieltjesNumerator_coeff {R : Type*} [CommRing R]
    (moment : ℕ → R) (n k : ℕ) (hk : k < n + 1) :
    (gramStieltjesNumerator moment n).coeff k =
      (momentHankelMatrix moment (n + 1)).adjugate ⟨k, hk⟩ (Fin.last n) := by
  classical
  exact Polynomial.ofFn_coeff_eq_val_of_lt _ hk

/-- The fraction-free numerator has degree at most `n`. -/
theorem gramStieltjesNumerator_natDegree_le {R : Type*} [CommRing R]
    (moment : ℕ → R) (n : ℕ) :
    (gramStieltjesNumerator moment n).natDegree ≤ n := by
  classical
  unfold gramStieltjesNumerator
  exact Nat.lt_succ_iff.mp
    (Polynomial.ofFn_natDegree_lt (Nat.succ_le_succ (Nat.zero_le n)) _)

private theorem momentPairing_gramStieltjesNumerator_X_pow_eq_mul_adjugate
    {R : Type*} [CommRing R] (moment : ℕ → R) (n : ℕ)
    (i : Fin (n + 1)) :
    momentPairing moment (gramStieltjesNumerator moment n)
        (Polynomial.X ^ (i : ℕ)) =
      (momentHankelMatrix moment (n + 1) *
          (momentHankelMatrix moment (n + 1)).adjugate) i (Fin.last n) := by
  classical
  rw [gramStieltjesNumerator, Polynomial.ofFn_eq_sum_monomial]
  simp only [map_sum, LinearMap.coe_sum, Finset.sum_apply,
    Polynomial.X_pow_eq_monomial, momentPairing_monomial, mul_one,
    Matrix.mul_apply, momentHankelMatrix_apply]
  apply Finset.sum_congr rfl
  intro j _
  calc
    (momentHankelMatrix moment (n + 1)).adjugate j (Fin.last n) *
        moment ((j : ℕ) + (i : ℕ)) =
      moment ((j : ℕ) + (i : ℕ)) *
        (momentHankelMatrix moment (n + 1)).adjugate j (Fin.last n) :=
          mul_comm _ _
    _ = moment ((i : ℕ) + (j : ℕ)) *
        (momentHankelMatrix moment (n + 1)).adjugate j (Fin.last n) := by
          rw [add_comm (j : ℕ) (i : ℕ)]

/-- The numerator is orthogonal to every pure power of degree below `n`. -/
theorem momentPairing_gramStieltjesNumerator_X_pow_eq_zero
    {R : Type*} [CommRing R] (moment : ℕ → R) (n : ℕ) (i : Fin n) :
    momentPairing moment (gramStieltjesNumerator moment n)
        (Polynomial.X ^ (i : ℕ)) = 0 := by
  have h := momentPairing_gramStieltjesNumerator_X_pow_eq_mul_adjugate
    moment n i.castSucc
  rw [Matrix.mul_adjugate] at h
  simpa using h

/-- Pairing the numerator with `X^n` gives the next Hankel determinant. -/
theorem momentPairing_gramStieltjesNumerator_X_pow_eq_det
    {R : Type*} [CommRing R] (moment : ℕ → R) (n : ℕ) :
    momentPairing moment (gramStieltjesNumerator moment n)
        (Polynomial.X ^ n) = momentHankelDet moment (n + 1) := by
  have h := momentPairing_gramStieltjesNumerator_X_pow_eq_mul_adjugate
    moment n (Fin.last n)
  rw [Matrix.mul_adjugate] at h
  simpa [momentHankelDet] using h

/-- The coefficient in degree `n` of the fraction-free numerator is the
order-`n` Hankel determinant. -/
theorem gramStieltjesNumerator_coeff_top {R : Type*} [CommRing R]
    (moment : ℕ → R) (n : ℕ) :
    (gramStieltjesNumerator moment n).coeff n = momentHankelDet moment n := by
  rw [gramStieltjesNumerator_coeff moment n n (Nat.lt_succ_self n),
    show (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Fin.last n by rfl,
    Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp [momentHankelDet, Fin.succAbove_last]

/-- Pairing the fraction-free numerator with any polynomial of degree at most
`n` extracts its top coefficient and multiplies it by the next Hankel
determinant. -/
theorem momentPairing_gramStieltjesNumerator_eq_coeff_mul_det
    {R : Type*} [CommRing R] (moment : ℕ → R) (n : ℕ) (q : R[X])
    (hq : q.natDegree ≤ n) :
    momentPairing moment (gramStieltjesNumerator moment n) q =
      q.coeff n * momentHankelDet moment (n + 1) := by
  calc
    momentPairing moment (gramStieltjesNumerator moment n) q =
        ∑ i ∈ range (n + 1), q.coeff i *
          momentPairing moment (gramStieltjesNumerator moment n)
            (Polynomial.X ^ i) := by
      conv_lhs => rw [q.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hq)]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Polynomial.smul_eq_C_mul, map_smul, smul_eq_mul]
    _ = q.coeff n * momentHankelDet moment (n + 1) := by
      rw [Finset.sum_range_succ]
      have hzero :
          (∑ i ∈ range n, q.coeff i *
            momentPairing moment (gramStieltjesNumerator moment n)
              (Polynomial.X ^ i)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [momentPairing_gramStieltjesNumerator_X_pow_eq_zero
          moment n ⟨i, Finset.mem_range.mp hi⟩, mul_zero]
      rw [hzero, zero_add,
        momentPairing_gramStieltjesNumerator_X_pow_eq_det]

/-- The self-pairing of the fraction-free numerator is the product of two
consecutive Hankel determinants. -/
theorem momentPairing_gramStieltjesNumerator_self
    {R : Type*} [CommRing R] (moment : ℕ → R) (n : ℕ) :
    momentPairing moment (gramStieltjesNumerator moment n)
        (gramStieltjesNumerator moment n) =
      momentHankelDet moment n * momentHankelDet moment (n + 1) := by
  rw [momentPairing_gramStieltjesNumerator_eq_coeff_mul_det moment n
    (gramStieltjesNumerator moment n)
    (gramStieltjesNumerator_natDegree_le moment n),
    gramStieltjesNumerator_coeff_top]

/-! ## Monic normalization over a field -/

/-- The Gram--Stieltjes normalization candidate obtained by dividing the
fraction-free numerator by its order-`n` Hankel determinant.  It is monic when
that determinant is nonzero. -/
def gramStieltjesPolynomial {K : Type*} [Field K]
    (moment : ℕ → K) (n : ℕ) : K[X] :=
  Polynomial.C (momentHankelDet moment n)⁻¹ *
    gramStieltjesNumerator moment n

/-- The normalized Gram--Stieltjes polynomial has degree at most `n`. -/
theorem gramStieltjesPolynomial_natDegree_le {K : Type*} [Field K]
    (moment : ℕ → K) (n : ℕ) :
    (gramStieltjesPolynomial moment n).natDegree ≤ n :=
  (Polynomial.natDegree_C_mul_le _ _).trans
    (gramStieltjesNumerator_natDegree_le moment n)

/-- If the leading Hankel determinant is nonzero, the normalized polynomial
has coefficient one in degree `n`. -/
theorem gramStieltjesPolynomial_coeff_top {K : Type*} [Field K]
    (moment : ℕ → K) (n : ℕ) (hdet : momentHankelDet moment n ≠ 0) :
    (gramStieltjesPolynomial moment n).coeff n = 1 := by
  rw [gramStieltjesPolynomial, Polynomial.coeff_C_mul,
    gramStieltjesNumerator_coeff_top, inv_mul_cancel₀ hdet]

/-- Nonvanishing of the order-`n` Hankel determinant makes the normalized
polynomial monic of exact degree `n`. -/
theorem gramStieltjesPolynomial_isMonicOfDegree {K : Type*} [Field K]
    (moment : ℕ → K) (n : ℕ) (hdet : momentHankelDet moment n ≠ 0) :
    Polynomial.IsMonicOfDegree (gramStieltjesPolynomial moment n) n := by
  rw [Polynomial.isMonicOfDegree_iff]
  exact ⟨gramStieltjesPolynomial_natDegree_le moment n,
    gramStieltjesPolynomial_coeff_top moment n hdet⟩

/-- The normalized polynomial is orthogonal to every pure power below its
degree. -/
theorem momentPairing_gramStieltjesPolynomial_X_pow_eq_zero
    {K : Type*} [Field K] (moment : ℕ → K) (n : ℕ) (i : Fin n) :
    momentPairing moment (gramStieltjesPolynomial moment n)
        (Polynomial.X ^ (i : ℕ)) = 0 := by
  rw [gramStieltjesPolynomial, ← Polynomial.smul_eq_C_mul, map_smul,
    LinearMap.smul_apply, smul_eq_mul,
    momentPairing_gramStieltjesNumerator_X_pow_eq_zero, mul_zero]

/-- The normalized polynomial is orthogonal to every polynomial of degree
strictly below `n`. -/
theorem momentPairing_gramStieltjesPolynomial_eq_zero
    {K : Type*} [Field K] (moment : ℕ → K) (n : ℕ) (q : K[X])
    (hq : q.natDegree < n) :
    momentPairing moment (gramStieltjesPolynomial moment n) q = 0 := by
  by_cases hn : n = 0
  · omega
  calc
    momentPairing moment (gramStieltjesPolynomial moment n) q =
        ∑ i ∈ range n, q.coeff i *
          momentPairing moment (gramStieltjesPolynomial moment n)
            (Polynomial.X ^ i) := by
      conv_lhs => rw [q.as_sum_range_C_mul_X_pow' hq]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Polynomial.smul_eq_C_mul, map_smul, smul_eq_mul]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [momentPairing_gramStieltjesPolynomial_X_pow_eq_zero
        moment n ⟨i, Finset.mem_range.mp hi⟩, mul_zero]

/-- The normalized Gram--Stieltjes polynomial is the unique monic polynomial
of degree `n` orthogonal to every lower-degree polynomial. -/
theorem eq_gramStieltjesPolynomial_of_isMonicOfDegree_of_orthogonal
    {K : Type*} [Field K] (moment : ℕ → K) (n : ℕ)
    (hdet : momentHankelDet moment n ≠ 0) (p : K[X])
    (hp : Polynomial.IsMonicOfDegree p n)
    (hortho : ∀ q : K[X], q.natDegree < n →
      momentPairing moment p q = 0) :
    p = gramStieltjesPolynomial moment n := by
  have hP := gramStieltjesPolynomial_isMonicOfDegree moment n hdet
  cases n with
  | zero =>
      rw [Polynomial.isMonicOfDegree_zero_iff] at hp hP
      exact hp.trans hP.symm
  | succ n =>
      let dpoly := p - gramStieltjesPolynomial moment (n + 1)
      have hdNat : dpoly.natDegree < n + 1 := by
        exact hp.natDegree_sub_lt (Nat.succ_ne_zero n) hP
      have hdMem : dpoly ∈ Polynomial.degreeLT K (n + 1) := by
        rw [Polynomial.mem_degreeLT]
        by_cases hd0 : dpoly = 0
        · simp [hd0]
        · rw [Polynomial.degree_eq_natDegree hd0, Nat.cast_lt]
          exact hdNat
      let d : Polynomial.degreeLT K (n + 1) := ⟨dpoly, hdMem⟩
      have hnon :=
        (finiteMomentPairing_nondegenerate_iff moment (n + 1)).2 hdet
      have hd : d = 0 := hnon.1 d fun q ↦ by
        have hqNat : (q : K[X]).natDegree < n + 1 := by
          by_cases hq0 : (q : K[X]) = 0
          · simp [hq0]
          · have hqMem := q.property
            rw [Polynomial.mem_degreeLT,
              Polynomial.degree_eq_natDegree hq0, Nat.cast_lt] at hqMem
            exact hqMem
        change momentPairing moment dpoly (q : K[X]) = 0
        simp only [dpoly, map_sub, LinearMap.sub_apply]
        rw [hortho (q : K[X]) hqNat,
          momentPairing_gramStieltjesPolynomial_eq_zero moment (n + 1)
            (q : K[X]) hqNat, sub_zero]
      have hdpoly : dpoly = 0 := by
        exact Subtype.ext_iff.mp hd
      exact sub_eq_zero.mp hdpoly

/-- The self-pairing of the monic Gram--Stieltjes polynomial is the quotient
of consecutive Hankel determinants. -/
theorem momentPairing_gramStieltjesPolynomial_self
    {K : Type*} [Field K] (moment : ℕ → K) (n : ℕ)
    (hdet : momentHankelDet moment n ≠ 0) :
    momentPairing moment (gramStieltjesPolynomial moment n)
        (gramStieltjesPolynomial moment n) =
      momentHankelDet moment (n + 1) / momentHankelDet moment n := by
  rw [gramStieltjesPolynomial, ← Polynomial.smul_eq_C_mul]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [momentPairing_gramStieltjesNumerator_self]
  field_simp [hdet]

/-- Consecutive nonzero Hankel determinants give a nonzero self-pairing for
the monic Gram--Stieltjes polynomial. -/
theorem momentPairing_gramStieltjesPolynomial_self_ne_zero
    {K : Type*} [Field K] (moment : ℕ → K) (n : ℕ)
    (hdet : momentHankelDet moment n ≠ 0)
    (hdet' : momentHankelDet moment (n + 1) ≠ 0) :
    momentPairing moment (gramStieltjesPolynomial moment n)
        (gramStieltjesPolynomial moment n) ≠ 0 := by
  rw [momentPairing_gramStieltjesPolynomial_self moment n hdet]
  exact div_ne_zero hdet' hdet

end

end Fabius
