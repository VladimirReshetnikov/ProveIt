import ExponentialIdentities.TwoBaseIntegerExponent.GeometricNewtonInterpolation

/-!
# Finite q-Newton endpoint defect

This file isolates the finite polynomial identity behind the one-edge q-Newton model.
There is no infinite series or analytic convergence input.
-/

namespace LeanProofs.TwoBaseIntegerExponent
namespace QNewtonEndpointDefect

open scoped BigOperators
open Finset Polynomial

variable {F : Type*} [Field F]

noncomputable section

/-- The monic Newton basis polynomial with geometric nodes `1, q, ..., q^(n-1)`. -/
def geometricNodeBasis (q : F) (n : ℕ) : F[X] :=
  ∏ j ∈ range n, (X - C (q ^ j))

@[simp] theorem geometricNodeBasis_zero (q : F) : geometricNodeBasis q 0 = 1 := by
  simp [geometricNodeBasis]

theorem geometricNodeBasis_succ (q : F) (n : ℕ) :
    geometricNodeBasis q (n + 1) =
      geometricNodeBasis q n * (X - C (q ^ n)) := by
  simp [geometricNodeBasis, prod_range_succ]

/-- Substitution `X ↦ qX`. -/
def dilate (q : F) (P : F[X]) : F[X] := P.comp (C q * X)

@[simp] theorem eval_dilate (q : F) (P : F[X]) (x : F) :
    (dilate q P).eval x = P.eval (q * x) := by
  simp [dilate]

/-- Scaling the geometric basis shifts all but the first node back by one. -/
theorem dilate_geometricNodeBasis_succ (q : F) (n : ℕ) :
    dilate q (geometricNodeBasis q (n + 1)) =
      C (q ^ n) * (C q * X - 1) * geometricNodeBasis q n := by
  induction n with
  | zero =>
      simp [geometricNodeBasis, dilate]
  | succ n ih =>
      rw [geometricNodeBasis_succ, dilate, Polynomial.mul_comp]
      change dilate q (geometricNodeBasis q (n + 1)) *
          ((X - C (q ^ (n + 1))).comp (C q * X)) = _
      rw [ih, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp,
        geometricNodeBasis_succ]
      rw [pow_succ]
      simp only [map_mul]
      ring

/-- The Newton denominator at the endpoint `q^n`. -/
def geometricNodeDenominator (q : F) (n : ℕ) : F :=
  (geometricNodeBasis q n).eval (q ^ n)

@[simp] theorem geometricNodeDenominator_zero (q : F) :
    geometricNodeDenominator q 0 = 1 := by
  simp [geometricNodeDenominator]

theorem geometricNodeDenominator_eq_prod (q : F) (n : ℕ) :
    geometricNodeDenominator q n =
      ∏ j ∈ range n, (q ^ n - q ^ j) := by
  rw [geometricNodeDenominator, geometricNodeBasis]
  simp only [eval_prod, eval_sub, eval_X, eval_C]

theorem geometricNodeDenominator_succ (q : F) (n : ℕ) :
    geometricNodeDenominator q (n + 1) =
      geometricNodeDenominator q n * (q ^ n * (q ^ (n + 1) - 1)) := by
  have h := congrArg (Polynomial.eval (q ^ n))
    (dilate_geometricNodeBasis_succ q n)
  simp only [eval_dilate, eval_mul, eval_C, eval_sub, eval_X, eval_one] at h
  simpa [geometricNodeDenominator, pow_succ, mul_comm, mul_left_comm, mul_assoc] using h

/-- The numerator of the geometric Newton coefficient. -/
def qNewtonNumerator (q r : F) (n : ℕ) : F :=
  ∏ j ∈ range n, (r - q ^ j)

@[simp] theorem qNewtonNumerator_zero (q r : F) :
    qNewtonNumerator q r 0 = 1 := by
  simp [qNewtonNumerator]

theorem qNewtonNumerator_succ (q r : F) (n : ℕ) :
    qNewtonNumerator q r (n + 1) =
      qNewtonNumerator q r n * (r - q ^ n) := by
  simp [qNewtonNumerator, prod_range_succ]

/-- The standard coefficient of the finite geometric Newton interpolant. -/
def qNewtonCoefficient (q r : F) (n : ℕ) : F :=
  qNewtonNumerator q r n / geometricNodeDenominator q n

@[simp] theorem qNewtonCoefficient_zero (q r : F) :
    qNewtonCoefficient q r 0 = 1 := by
  simp [qNewtonCoefficient]

/-- The product formula for the Newton coefficient gives its one-step recurrence. -/
theorem qNewtonCoefficient_succ (q r : F) (n : ℕ)
    (hden : geometricNodeDenominator q n ≠ 0)
    (hden' : geometricNodeDenominator q (n + 1) ≠ 0) :
    qNewtonCoefficient q r (n + 1) =
      qNewtonCoefficient q r n * (r - q ^ n) /
        (q ^ n * (q ^ (n + 1) - 1)) := by
  have hfactor : q ^ n * (q ^ (n + 1) - 1) ≠ 0 := by
    intro hf
    apply hden'
    rw [geometricNodeDenominator_succ, hf, mul_zero]
  rw [qNewtonCoefficient, qNewtonCoefficient, qNewtonNumerator_succ,
    geometricNodeDenominator_succ]
  let a := qNewtonNumerator q r n
  let d := geometricNodeDenominator q n
  let f := q ^ n * (q ^ (n + 1) - 1)
  change a * (r - q ^ n) / (d * f) = (a / d) * (r - q ^ n) / f
  have hd : d ≠ 0 := hden
  have hf : f ≠ 0 := hfactor
  field_simp [hd, hf]

/-- The coefficient recurrence, written in the cancellation form used by the endpoint defect. -/
theorem qNewtonCoefficient_balance (q r : F) (n : ℕ)
    (hden : geometricNodeDenominator q n ≠ 0)
    (hden' : geometricNodeDenominator q (n + 1) ≠ 0) :
    (q ^ n - r) * qNewtonCoefficient q r n =
      -(qNewtonCoefficient q r (n + 1) * q ^ n * (q ^ (n + 1) - 1)) := by
  have hfactor : q ^ n * (q ^ (n + 1) - 1) ≠ 0 := by
    intro hf
    apply hden'
    rw [geometricNodeDenominator_succ, hf, mul_zero]
  rw [qNewtonCoefficient_succ q r n hden hden']
  symm
  calc
    -((qNewtonCoefficient q r n * (r - q ^ n) /
          (q ^ n * (q ^ (n + 1) - 1))) * q ^ n * (q ^ (n + 1) - 1)) =
        -((qNewtonCoefficient q r n * (r - q ^ n) /
          (q ^ n * (q ^ (n + 1) - 1))) *
            (q ^ n * (q ^ (n + 1) - 1))) := by ring
    _ = -(qNewtonCoefficient q r n * (r - q ^ n)) := by
      rw [div_mul_cancel₀ _ hfactor]
    _ = (q ^ n - r) * qNewtonCoefficient q r n := by ring

/-- The degree-`N` finite geometric Newton interpolant. -/
def qNewtonPolynomial (q r : F) (N : ℕ) : F[X] :=
  ∑ n ∈ range (N + 1),
    C (qNewtonCoefficient q r n) * geometricNodeBasis q n

@[simp] theorem qNewtonPolynomial_zero (q r : F) :
    qNewtonPolynomial q r 0 = 1 := by
  simp [qNewtonPolynomial]

theorem qNewtonPolynomial_succ (q r : F) (N : ℕ) :
    qNewtonPolynomial q r (N + 1) =
      qNewtonPolynomial q r N +
        C (qNewtonCoefficient q r (N + 1)) * geometricNodeBasis q (N + 1) := by
  simp [qNewtonPolynomial, sum_range_succ]

/-- Exact finite endpoint defect for geometric Newton interpolation. -/
theorem qNewtonPolynomial_endpoint_dilation_defect
    (q r : F) (hden : ∀ n, geometricNodeDenominator q n ≠ 0) (N : ℕ) :
    dilate q (qNewtonPolynomial q r N) - C r * qNewtonPolynomial q r N =
      C ((q ^ N - r) * qNewtonCoefficient q r N) * geometricNodeBasis q N := by
  induction N with
  | zero =>
      simp [dilate]
  | succ N ih =>
      rw [qNewtonPolynomial_succ]
      calc
        dilate q
              (qNewtonPolynomial q r N +
                C (qNewtonCoefficient q r (N + 1)) *
                  geometricNodeBasis q (N + 1)) -
            C r *
              (qNewtonPolynomial q r N +
                C (qNewtonCoefficient q r (N + 1)) *
                  geometricNodeBasis q (N + 1)) =
            (dilate q (qNewtonPolynomial q r N) -
                C r * qNewtonPolynomial q r N) +
              (C (qNewtonCoefficient q r (N + 1)) *
                  dilate q (geometricNodeBasis q (N + 1)) -
                C r *
                  (C (qNewtonCoefficient q r (N + 1)) *
                    geometricNodeBasis q (N + 1))) := by
              simp only [dilate, Polynomial.add_comp, Polynomial.mul_comp,
                Polynomial.C_comp]
              ring
        _ = C ((q ^ (N + 1) - r) * qNewtonCoefficient q r (N + 1)) *
              geometricNodeBasis q (N + 1) := by
          rw [ih, dilate_geometricNodeBasis_succ, geometricNodeBasis_succ,
            qNewtonCoefficient_balance q r N (hden N) (hden (N + 1))]
          simp only [map_mul, map_neg, map_sub, map_pow, map_one]
          ring

end
end QNewtonEndpointDefect
end LeanProofs.TwoBaseIntegerExponent
