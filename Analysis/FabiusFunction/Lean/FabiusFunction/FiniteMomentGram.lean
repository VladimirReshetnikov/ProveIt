import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
# Finite moment functionals and Hankel Gram forms

This module isolates the finite linear algebra shared by moment problems,
orthogonal polynomials, Gaussian quadrature, and finite Jacobi recurrences.
For an arbitrary scalar sequence `moment : ℕ → R`, it defines

* `momentFunctional moment`, the linear functional sending `X ^ n` to
  `moment n`;
* `momentPairing moment p q = momentFunctional moment (p * q)`;
* `momentHankelMatrix moment n = (moment (i + j))_{i,j<n}` and its
  determinant;
* the restriction of the pairing to polynomials of degree `< n`.

The monomial basis identifies the matrix of that restricted pairing exactly
with the Hankel matrix.  Consequently, over an integral domain, nonvanishing
of the finite Hankel determinant is equivalent to nondegeneracy of the
degree-bounded moment pairing.

Everything here is finite algebra.  No measure, positivity, root theorem,
quadrature rule, infinite continued fraction, or convergence assertion is
used.
-/

set_option autoImplicit false

open Finset Polynomial
open LinearMap (BilinForm)
open scoped BigOperators

namespace Fabius

noncomputable section

/-! ## The polynomial moment functional -/

/-- The linear functional on polynomials determined by a scalar moment
sequence.  It maps `X ^ n` to `moment n`. -/
def momentFunctional {R : Type*} [Semiring R]
    (moment : ℕ → R) : R[X] →ₗ[R] R :=
  Polynomial.lsum fun n ↦ LinearMap.mulRight R (moment n)

/-- Coefficient-sum form of the polynomial moment functional. -/
@[simp]
theorem momentFunctional_apply {R : Type*} [Semiring R]
    (moment : ℕ → R) (p : R[X]) :
    momentFunctional moment p = p.sum fun n a ↦ a * moment n :=
  rfl

/-- The moment functional on a monomial. -/
@[simp]
theorem momentFunctional_monomial {R : Type*} [Semiring R]
    (moment : ℕ → R) (n : ℕ) (a : R) :
    momentFunctional moment (Polynomial.monomial n a) = a * moment n := by
  simp [momentFunctional]

/-- The moment functional on a constant polynomial. -/
@[simp]
theorem momentFunctional_C {R : Type*} [Semiring R]
    (moment : ℕ → R) (a : R) :
    momentFunctional moment (Polynomial.C a) = a * moment 0 := by
  simpa only [Polynomial.monomial_zero_left] using
    momentFunctional_monomial moment 0 a

/-- The moment functional sends a pure power to the corresponding moment. -/
@[simp]
theorem momentFunctional_X_pow {R : Type*} [Semiring R]
    (moment : ℕ → R) (n : ℕ) :
    momentFunctional moment (Polynomial.X ^ n) = moment n := by
  rw [Polynomial.X_pow_eq_monomial, momentFunctional_monomial, one_mul]

/-- Every linear functional on polynomials is recovered from its values on
the pure powers of `X`. -/
theorem momentFunctional_of_linearMap {R : Type*} [Semiring R]
    (L : R[X] →ₗ[R] R) :
    momentFunctional (fun n ↦ L (Polynomial.X ^ n)) = L := by
  apply Polynomial.lhom_ext'
  intro n
  apply LinearMap.ext
  intro a
  simp only [LinearMap.comp_apply]
  rw [← Polynomial.smul_X_eq_monomial]
  simp only [map_smul, momentFunctional_X_pow]

/-- A scalar moment sequence is uniquely determined by its polynomial moment
functional. -/
theorem momentFunctional_injective {R : Type*} [Semiring R] :
    Function.Injective (momentFunctional : (ℕ → R) → R[X] →ₗ[R] R) := by
  intro a b h
  funext n
  have hn := congrArg (fun L : R[X] →ₗ[R] R ↦ L (Polynomial.X ^ n)) h
  simpa only [momentFunctional_X_pow] using hn

/-- Explicit support-sum form of the moment functional. -/
theorem momentFunctional_eq_sum_support {R : Type*} [Semiring R]
    (moment : ℕ → R) (p : R[X]) :
    momentFunctional moment p =
      ∑ n ∈ p.support, p.coeff n * moment n := by
  rw [momentFunctional_apply, Polynomial.sum_def]

/-- Explicit bounded-range form of the moment functional. -/
theorem momentFunctional_eq_sum_range {R : Type*} [Semiring R]
    (moment : ℕ → R) (p : R[X]) (N : ℕ) (hdeg : p.natDegree ≤ N) :
    momentFunctional moment p =
      ∑ n ∈ range (N + 1), p.coeff n * moment n := by
  rw [momentFunctional_apply, Polynomial.sum_over_range' p
    (fun n ↦ zero_mul (moment n)) (N + 1) (Nat.lt_succ_of_le hdeg)]

/-- Polynomial base change commutes with the moment functional. -/
theorem momentFunctional_map {R S : Type*} [Semiring R] [Semiring S]
    (φ : R →+* S) (moment : ℕ → R) (p : R[X]) :
    momentFunctional (fun n ↦ φ (moment n)) (p.map φ) =
      φ (momentFunctional moment p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.map_add, map_add, hp, hq]
  | monomial n a => simp

/-! ## The moment pairing and its Hankel matrix -/

/-- The symmetric bilinear pairing induced by a moment functional:
`⟪p,q⟫ = L(pq)`. -/
def momentPairing {R : Type*} [CommSemiring R]
    (moment : ℕ → R) : BilinForm R R[X] :=
  LinearMap.mk₂ R (fun p q ↦ momentFunctional moment (p * q))
    (fun p q r ↦ by simp only [add_mul, map_add])
    (fun c p q ↦ by simp only [smul_mul_assoc, map_smul])
    (fun p q r ↦ by simp only [mul_add, map_add])
    (fun c p q ↦ by simp only [mul_smul_comm, map_smul])

/-- Evaluation formula for the moment pairing. -/
@[simp]
theorem momentPairing_apply {R : Type*} [CommSemiring R]
    (moment : ℕ → R) (p q : R[X]) :
    momentPairing moment p q = momentFunctional moment (p * q) :=
  rfl

/-- The moment pairing of two monomials. -/
@[simp]
theorem momentPairing_monomial {R : Type*} [CommSemiring R]
    (moment : ℕ → R) (i j : ℕ) (a b : R) :
    momentPairing moment (Polynomial.monomial i a)
        (Polynomial.monomial j b) = (a * b) * moment (i + j) := by
  rw [momentPairing_apply, Polynomial.monomial_mul_monomial,
    momentFunctional_monomial]

/-- The moment pairing of two pure powers. -/
@[simp]
theorem momentPairing_X_pow {R : Type*} [CommSemiring R]
    (moment : ℕ → R) (i j : ℕ) :
    momentPairing moment (Polynomial.X ^ i) (Polynomial.X ^ j) =
      moment (i + j) := by
  rw [momentPairing_apply, ← pow_add, momentFunctional_X_pow]

/-- The moment pairing is symmetric. -/
theorem momentPairing_isSymm {R : Type*} [CommSemiring R]
    (moment : ℕ → R) : (momentPairing moment).IsSymm := by
  constructor
  intro p q
  rw [momentPairing_apply, momentPairing_apply, mul_comm]

/-- The order-`n` Hankel matrix of a moment sequence. -/
def momentHankelMatrix {R : Type*} (moment : ℕ → R) (n : ℕ) :
    Matrix (Fin n) (Fin n) R :=
  fun i j ↦ moment ((i : ℕ) + (j : ℕ))

/-- Entry formula for the moment Hankel matrix. -/
@[simp]
theorem momentHankelMatrix_apply {R : Type*} (moment : ℕ → R)
    (n : ℕ) (i j : Fin n) :
    momentHankelMatrix moment n i j = moment ((i : ℕ) + (j : ℕ)) :=
  rfl

/-- The Hankel matrix of a scalar moment sequence is symmetric. -/
theorem momentHankelMatrix_transpose {R : Type*}
    (moment : ℕ → R) (n : ℕ) :
    (momentHankelMatrix moment n).transpose = momentHankelMatrix moment n := by
  ext i j
  simp only [Matrix.transpose_apply, momentHankelMatrix_apply, add_comm]

/-- The order-`n` Hankel matrix is the leading principal submatrix of the
order-`n+1` Hankel matrix. -/
@[simp]
theorem momentHankelMatrix_succ_submatrix {R : Type*}
    (moment : ℕ → R) (n : ℕ) :
    (momentHankelMatrix moment (n + 1)).submatrix Fin.castSucc Fin.castSucc =
      momentHankelMatrix moment n := by
  ext i j
  rfl

/-- Entrywise scalar maps commute with formation of a Hankel matrix. -/
theorem momentHankelMatrix_map {R S : Type*} (φ : R → S)
    (moment : ℕ → R) (n : ℕ) :
    (momentHankelMatrix moment n).map φ =
      momentHankelMatrix (fun k ↦ φ (moment k)) n := by
  ext i j
  rfl

/-- The order-`n` Hankel determinant of a moment sequence. -/
def momentHankelDet {R : Type*} [CommRing R]
    (moment : ℕ → R) (n : ℕ) : R :=
  (momentHankelMatrix moment n).det

/-- The empty Hankel determinant is one. -/
@[simp]
theorem momentHankelDet_zero {R : Type*} [CommRing R]
    (moment : ℕ → R) : momentHankelDet moment 0 = 1 := by
  rw [momentHankelDet, Matrix.det_isEmpty]

/-- Ring homomorphisms commute with finite Hankel determinants. -/
theorem map_momentHankelDet {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (moment : ℕ → R) (n : ℕ) :
    φ (momentHankelDet moment n) =
      momentHankelDet (fun k ↦ φ (moment k)) n := by
  rw [momentHankelDet, momentHankelDet, RingHom.map_det]
  change ((momentHankelMatrix moment n).map φ).det = _
  rw [momentHankelMatrix_map]

/-- The moment pairing restricted to polynomials of degree strictly less
than `n`. -/
def finiteMomentPairing {R : Type*} [CommSemiring R]
    (moment : ℕ → R) (n : ℕ) : BilinForm R (Polynomial.degreeLT R n) :=
  (momentPairing moment).restrict (Polynomial.degreeLT R n)

/-- In the monomial basis, the finite moment pairing has exactly the Hankel
matrix of the moment sequence. -/
theorem finiteMomentPairing_toMatrix {R : Type*} [CommSemiring R]
    (moment : ℕ → R) (n : ℕ) :
    LinearMap.BilinForm.toMatrix (Polynomial.degreeLT.basis R n)
        (finiteMomentPairing moment n) = momentHankelMatrix moment n := by
  ext i j
  rw [LinearMap.BilinForm.toMatrix_apply]
  simpa [finiteMomentPairing] using
    momentPairing_X_pow moment (i : ℕ) (j : ℕ)

/-- Over an integral domain, the finite moment pairing is nondegenerate
exactly when the corresponding Hankel determinant is nonzero. -/
theorem finiteMomentPairing_nondegenerate_iff {R : Type*}
    [CommRing R] [IsDomain R] (moment : ℕ → R) (n : ℕ) :
    (finiteMomentPairing moment n).Nondegenerate ↔
      momentHankelDet moment n ≠ 0 := by
  rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero
    (Polynomial.degreeLT.basis R n), finiteMomentPairing_toMatrix]
  rfl

end

end Fabius
