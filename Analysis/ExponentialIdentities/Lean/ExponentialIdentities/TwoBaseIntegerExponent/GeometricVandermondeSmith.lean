import ExponentialIdentities.TwoBaseIntegerExponent.SignedProgressionDeterminant
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Exact Smith form of the geometric Vandermonde

This module gives an explicit determinant-one two-sided reduction of the geometric
Vandermonde matrix to the diagonal claimed in report 17.  It also proves the integral
q-Pascal identity, divisibility order, and positivity of the Smith factors.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open scoped BigOperators
open Finset Matrix Polynomial

noncomputable section

/-- Gaussian binomial coefficients, defined by the integral q-Pascal recurrence
`[n+1,k+1]_q = [n,k]_q + q^(k+1) [n,k+1]_q`. -/
def qPascal (q : ℤ) : ℕ → ℕ → ℤ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => qPascal q n k + q ^ (k + 1) * qPascal q n (k + 1)

@[simp] theorem qPascal_zero (q : ℤ) (n : ℕ) : qPascal q n 0 = 1 := by
  cases n <;> rfl

@[simp] theorem qPascal_zero_succ (q : ℤ) (k : ℕ) : qPascal q 0 (k + 1) = 0 := rfl

@[simp] theorem qPascal_succ_succ (q : ℤ) (n k : ℕ) :
    qPascal q (n + 1) (k + 1) =
      qPascal q n k + q ^ (k + 1) * qPascal q n (k + 1) := rfl

theorem qPascal_eq_zero_of_lt (q : ℤ) {n k : ℕ} (h : n < k) :
    qPascal q n k = 0 := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero => omega
      | succ k => rfl
  | succ n ih =>
      cases k with
      | zero => omega
      | succ k =>
          rw [qPascal_succ_succ, ih (by omega), ih (by omega)]
          ring

/-- Product `∏_{r=1}^k (q^r-1)`. -/
def qFactorProduct (q : ℤ) (k : ℕ) : ℤ :=
  ∏ r ∈ Finset.range k, (q ^ (r + 1) - 1)

/-- Product `∏_{r=0}^{k-1} (q^(n-r)-1)`, written without truncated subtraction
under the intended hypothesis `k ≤ n`. -/
def qNumeratorProduct (q : ℤ) (n k : ℕ) : ℤ :=
  ∏ r ∈ Finset.range k, (q ^ (n - r) - 1)

@[simp] theorem qFactorProduct_zero (q : ℤ) : qFactorProduct q 0 = 1 := by
  simp [qFactorProduct]

@[simp] theorem qNumeratorProduct_zero (q : ℤ) (n : ℕ) :
    qNumeratorProduct q n 0 = 1 := by
  simp [qNumeratorProduct]

theorem qFactorProduct_succ (q : ℤ) (k : ℕ) :
    qFactorProduct q (k + 1) = qFactorProduct q k * (q ^ (k + 1) - 1) := by
  simp [qFactorProduct, Finset.prod_range_succ]

theorem qNumeratorProduct_succ_right (q : ℤ) (n k : ℕ) :
    qNumeratorProduct q n (k + 1) =
      qNumeratorProduct q n k * (q ^ (n - k) - 1) := by
  simp [qNumeratorProduct, Finset.prod_range_succ]

theorem qNumeratorProduct_succ_left (q : ℤ) (n k : ℕ) :
    qNumeratorProduct q (n + 1) (k + 1) =
      (q ^ (n + 1) - 1) * qNumeratorProduct q n k := by
  rw [qNumeratorProduct, qNumeratorProduct, Finset.prod_range_succ']
  have hshift :
      (∏ r ∈ Finset.range k, (q ^ (n + 1 - (r + 1)) - 1)) =
        ∏ r ∈ Finset.range k, (q ^ (n - r) - 1) := by
    apply Finset.prod_congr rfl
    intro r hr
    congr 2
    omega
  rw [hshift]
  simp only [Nat.sub_zero]
  ring

/-- Integral q-binomial product identity. -/
theorem qPascal_mul_qFactorProduct (q : ℤ) {n k : ℕ} (hk : k ≤ n) :
    qPascal q n k * qFactorProduct q k = qNumeratorProduct q n k := by
  induction n generalizing k with
  | zero =>
      have : k = 0 := by omega
      subst k
      simp
  | succ n ih =>
      cases k with
      | zero => simp
      | succ k =>
          have hkn : k ≤ n := by omega
          rw [qPascal_succ_succ, qFactorProduct_succ, qNumeratorProduct_succ_left q n k]
          rw [add_mul]
          rw [← mul_assoc (qPascal q n k), ih hkn]
          by_cases htop : k + 1 ≤ n
          · rw [← qFactorProduct_succ q k]
            rw [mul_assoc (q ^ (k + 1)) (qPascal q n (k + 1)), ih htop]
            rw [qNumeratorProduct_succ_right q n k]
            have hpow : q ^ (k + 1) * q ^ (n - k) = q ^ (n + 1) := by
              calc
                q ^ (k + 1) * q ^ (n - k) = q ^ ((k + 1) + (n - k)) :=
                  (pow_add q (k + 1) (n - k)).symm
                _ = q ^ (n + 1) := by congr 1; omega
            calc
              qNumeratorProduct q n k * (q ^ (k + 1) - 1) +
                    q ^ (k + 1) *
                      (qNumeratorProduct q n k * (q ^ (n - k) - 1)) =
                  qNumeratorProduct q n k *
                    (q ^ (k + 1) * q ^ (n - k) - 1) := by ring
              _ = qNumeratorProduct q n k * (q ^ (n + 1) - 1) := by rw [hpow]
              _ = (q ^ (n + 1) - 1) * qNumeratorProduct q n k := by ring
          · have hkeq : k = n := by omega
            subst k
            rw [qPascal_eq_zero_of_lt q (Nat.lt_succ_self n)]
            rw [mul_zero, zero_mul, add_zero]
            ring

/-! ## Exact integral matrix equivalence -/

/-- The Newton polynomial with geometric nodes `1,q,...,q^(j-1)`. -/
def qNewtonPolynomial (q : ℤ) (j : ℕ) : ℤ[X] :=
  ∏ r ∈ Finset.range j, (X - C (q ^ r))

theorem qNewtonPolynomial_monic (q : ℤ) (j : ℕ) :
    (qNewtonPolynomial q j).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro r _
  exact Polynomial.monic_X_sub_C _

theorem qNewtonPolynomial_natDegree (q : ℤ) (j : ℕ) :
    (qNewtonPolynomial q j).natDegree = j := by
  rw [qNewtonPolynomial, Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
  simp

@[simp] theorem qNewtonPolynomial_eval (q : ℤ) (i j : ℕ) :
    (qNewtonPolynomial q j).eval (q ^ i) =
      ∏ r ∈ Finset.range j, (q ^ i - q ^ r) := by
  simp only [qNewtonPolynomial, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]

/-- The diagonal factor in report 17, initially written as its Newton-product content. -/
def qSmithFactor (q : ℤ) (j : ℕ) : ℤ :=
  (∏ r ∈ Finset.range j, q ^ r) * qFactorProduct q j

theorem qSmithFactor_report_formula (q : ℤ) (j : ℕ) :
    qSmithFactor q j = q ^ (j.choose 2) * ∏ r ∈ Finset.range j, (q ^ (r + 1) - 1) := by
  rw [qSmithFactor, qFactorProduct]
  congr 1
  calc
    (∏ r ∈ Finset.range j, q ^ r) = q ^ (∑ r ∈ Finset.range j, r) :=
      Finset.prod_pow_eq_pow_sum (Finset.range j) (fun r ↦ r) q
    _ = q ^ (j.choose 2) := by rw [Finset.sum_range_id, Nat.choose_two_right]

theorem qSmithFactor_zero (q : ℤ) : qSmithFactor q 0 = 1 := by
  simp [qSmithFactor]

theorem qSmithFactor_succ (q : ℤ) (j : ℕ) :
    qSmithFactor q (j + 1) =
      qSmithFactor q j * (q ^ j * (q ^ (j + 1) - 1)) := by
  simp only [qSmithFactor, qFactorProduct_succ, Finset.prod_range_succ]
  ring

theorem qSmithFactor_dvd_succ (q : ℤ) (j : ℕ) :
    qSmithFactor q j ∣ qSmithFactor q (j + 1) := by
  rw [qSmithFactor_succ]
  exact dvd_mul_right _ _

theorem qSmithFactor_pos {q : ℤ} (hq : 2 ≤ q) (j : ℕ) : 0 < qSmithFactor q j := by
  rw [qSmithFactor]
  apply mul_pos
  · apply Finset.prod_pos
    intro r _
    exact pow_pos (by omega) r
  · apply Finset.prod_pos
    intro r _
    exact sub_pos.mpr (one_lt_pow₀ (by omega : (1 : ℤ) < q) (by omega))

theorem qNewtonPolynomial_eval_eq_zero_of_lt (q : ℤ) {i j : ℕ} (hij : i < j) :
    (qNewtonPolynomial q j).eval (q ^ i) = 0 := by
  rw [qNewtonPolynomial_eval]
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hij)
  ring

theorem qNewtonPolynomial_eval_factor (q : ℤ) {i j : ℕ} (hji : j ≤ i) :
    (qNewtonPolynomial q j).eval (q ^ i) = qPascal q i j * qSmithFactor q j := by
  rw [qNewtonPolynomial_eval, qSmithFactor]
  have hfactor :
      (∏ r ∈ Finset.range j, (q ^ i - q ^ r)) =
        (∏ r ∈ Finset.range j, q ^ r) *
          ∏ r ∈ Finset.range j, (q ^ (i - r) - 1) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro r hr
    apply geometric_pow_sub_pow_factor
    exact (Finset.mem_range.mp hr).le.trans hji
  rw [hfactor]
  change (∏ r ∈ Finset.range j, q ^ r) * qNumeratorProduct q i j =
    qPascal q i j * ((∏ r ∈ Finset.range j, q ^ r) * qFactorProduct q j)
  rw [← qPascal_mul_qFactorProduct q hji]
  ring

/-- The lower unitriangular Gaussian-binomial matrix. -/
def qPascalMatrix (n : ℕ) (q : ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j ↦ qPascal q i j

@[simp] theorem qPascalMatrix_apply (n : ℕ) (q : ℤ) (i j : Fin n) :
    qPascalMatrix n q i j = qPascal q i j := rfl

theorem qPascal_self (q : ℤ) (n : ℕ) : qPascal q n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [qPascal_succ_succ, qPascal_eq_zero_of_lt q (Nat.lt_succ_self n), mul_zero, add_zero, ih]

theorem qPascalMatrix_lowerTriangular (n : ℕ) (q : ℤ) :
    (qPascalMatrix n q).BlockTriangular
      (fun i : Fin n ↦ (OrderDual.toDual i : (Fin n)ᵒᵈ)) := by
  intro i j hij
  rw [qPascalMatrix_apply]
  apply qPascal_eq_zero_of_lt
  exact hij

theorem det_qPascalMatrix (n : ℕ) (q : ℤ) : (qPascalMatrix n q).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (qPascalMatrix_lowerTriangular n q)]
  simp [qPascalMatrix_apply, qPascal_self]

/-- Coefficient matrix for the geometric Newton basis. -/
def qNewtonCoefficientMatrix (n : ℕ) (q : ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j ↦ (qNewtonPolynomial q j).coeff i

theorem det_qNewtonCoefficientMatrix (n : ℕ) (q : ℤ) :
    (qNewtonCoefficientMatrix n q).det = 1 := by
  apply Matrix.det_matrixOfPolynomials
  · intro i
    exact qNewtonPolynomial_natDegree q i
  · intro i
    exact qNewtonPolynomial_monic q i

/-- Evaluation matrix in the geometric Newton basis. -/
def qNewtonEvaluationMatrix (n : ℕ) (q : ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j ↦ (qNewtonPolynomial q j).eval (q ^ (i : ℕ))

theorem geometricVandermonde_mul_qNewtonCoefficientMatrix (n : ℕ) (q : ℤ) :
    geometricVandermondeMatrix n q * qNewtonCoefficientMatrix n q =
      qNewtonEvaluationMatrix n q := by
  rw [geometricVandermondeMatrix_eq_vandermonde]
  symm
  exact Matrix.eval_matrixOfPolynomials_eq_vandermonde_mul_matrixOfPolynomials
    (fun i : Fin n ↦ q ^ (i : ℕ)) (fun j : Fin n ↦ qNewtonPolynomial q j)
    (fun j ↦ (qNewtonPolynomial_natDegree q j).le)

/-- The claimed Smith diagonal. -/
def qSmithDiagonal (n : ℕ) (q : ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.diagonal fun j ↦ qSmithFactor q j

theorem qNewtonEvaluationMatrix_eq_qPascal_mul_diagonal (n : ℕ) (q : ℤ) :
    qNewtonEvaluationMatrix n q = qPascalMatrix n q * qSmithDiagonal n q := by
  ext i j
  by_cases hij : (i : ℕ) < (j : ℕ)
  · rw [qNewtonEvaluationMatrix, Matrix.of_apply,
      qNewtonPolynomial_eval_eq_zero_of_lt q hij]
    simp [qSmithDiagonal, qPascalMatrix_apply, qPascal_eq_zero_of_lt q hij]
  · have hji : (j : ℕ) ≤ (i : ℕ) := by omega
    rw [qNewtonEvaluationMatrix, Matrix.of_apply, qNewtonPolynomial_eval_factor q hji]
    simp [qSmithDiagonal, qPascalMatrix_apply]

/-- Integral two-sided equivalence with determinant-one transformations. -/
def IsUnimodularEquivalent {n : ℕ}
    (A D : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∃ L R : Matrix (Fin n) (Fin n) ℤ,
    L.det = 1 ∧ R.det = 1 ∧ L * A * R = D

/-- Exact finite Smith reduction for the geometric Vandermonde matrix.

Together with `qSmithFactor_dvd_succ` and `qSmithFactor_report_formula`, this says that the
displayed diagonal is already in Smith divisibility order. -/
theorem geometricVandermonde_isUnimodularEquivalent_qSmithDiagonal (n : ℕ) (q : ℤ) :
    IsUnimodularEquivalent (geometricVandermondeMatrix n q) (qSmithDiagonal n q) := by
  let G := qPascalMatrix n q
  let U := qNewtonCoefficientMatrix n q
  refine ⟨Matrix.adjugate G, U, ?_, det_qNewtonCoefficientMatrix n q, ?_⟩
  · rw [Matrix.det_adjugate, det_qPascalMatrix]
    simp
  · rw [Matrix.mul_assoc, geometricVandermonde_mul_qNewtonCoefficientMatrix]
    rw [qNewtonEvaluationMatrix_eq_qPascal_mul_diagonal]
    rw [← Matrix.mul_assoc, Matrix.adjugate_mul, det_qPascalMatrix]
    simp

end

end LeanProofs.TwoBaseIntegerExponent
