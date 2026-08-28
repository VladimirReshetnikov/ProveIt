import FabiusFunction.FabiusPrimitives
import FabiusFunction.VolterraPolynomial

/-!
# Polynomially weighted Fabius primitives

The universal polynomial--Volterra commutator becomes completely explicit for
the Fabius function because every higher Volterra integral is another dyadic
rescaling of the same signed extension.  This module records the all-real
signed formulas first and derives the bounded-function statements only as
local corollaries.

## Main results

* `volterraIntegral_polynomial_mul_extendedFabius` is the all-real polynomial
  formula for the signed extension.
* `volterraIntegral_pow_mul_extendedFabius` is its monomial specialization.
* `volterraIntegral_polynomial_mul_fabiusReal` transports the polynomial
  formula to the bounded function for every endpoint `x ≤ 1`.
* `volterraIntegral_pow_mul_fabiusReal` is the corresponding monomial formula.
-/

set_option autoImplicit false

open Set
open scoped Interval
open MeasureTheory

namespace Fabius

/-- For every real endpoint, a polynomial-weighted Volterra integral of the
signed Fabius extension is a finite Hasse-derivative combination of its closed
primitive ladder. -/
theorem volterraIntegral_polynomial_mul_extendedFabius
    (F : BoundedFabius) (hF : IsFabius F)
    (p : Polynomial ℝ) (n : ℕ) (x : ℝ) :
    volterraIntegral n (fun t => p.eval t * extendedFabius F t) 0 x =
      ∑ k ∈ Finset.range (p.natDegree + 1),
        ((-1 : ℝ) ^ k * ((n + 1).ascFactorial k : ℝ) *
            (Polynomial.hasseDeriv k p).eval x) *
          extendedFabiusPrimitive F (n + k + 1) x := by
  have hf : IntervalIntegrable (extendedFabius F) volume 0 x :=
    (extendedFabius_contDiff F hF).continuous.intervalIntegrable 0 x
  have h := volterraIntegral_polynomial_smul p n (extendedFabius F) 0 x hf
  have h' :
      volterraIntegral n (fun t => p.eval t * extendedFabius F t) 0 x =
        ∑ k ∈ Finset.range (p.natDegree + 1),
          ((-1 : ℝ) ^ k * ((n + 1).ascFactorial k : ℝ) *
              (Polynomial.hasseDeriv k p).eval x) *
            volterraIntegral (n + k) (extendedFabius F) 0 x := by
    simpa only [smul_eq_mul] using h
  calc
    _ = ∑ k ∈ Finset.range (p.natDegree + 1),
          ((-1 : ℝ) ^ k * ((n + 1).ascFactorial k : ℝ) *
              (Polynomial.hasseDeriv k p).eval x) *
            volterraIntegral (n + k) (extendedFabius F) 0 x := h'
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [volterraIntegral_extendedFabius_eq_extendedFabiusPrimitive F hF]

/-- Monomial weights give the explicit binomial/rising-factorial combination
of the signed Fabius primitive ladder at every real endpoint. -/
theorem volterraIntegral_pow_mul_extendedFabius
    (F : BoundedFabius) (hF : IsFabius F)
    (p n : ℕ) (x : ℝ) :
    volterraIntegral n (fun t => t ^ p * extendedFabius F t) 0 x =
      ∑ k ∈ Finset.range (p + 1),
        ((-1 : ℝ) ^ k * ((n + 1).ascFactorial k : ℝ) *
            (p.choose k : ℝ) * x ^ (p - k)) *
          extendedFabiusPrimitive F (n + k + 1) x := by
  have hf : IntervalIntegrable (extendedFabius F) volume 0 x :=
    (extendedFabius_contDiff F hF).continuous.intervalIntegrable 0 x
  have h := volterraIntegral_pow_smul p n (extendedFabius F) 0 x hf
  have h' :
      volterraIntegral n (fun t => t ^ p * extendedFabius F t) 0 x =
        ∑ k ∈ Finset.range (p + 1),
          ((-1 : ℝ) ^ k * ((n + 1).ascFactorial k : ℝ) *
              (p.choose k : ℝ) * x ^ (p - k)) *
            volterraIntegral (n + k) (extendedFabius F) 0 x := by
    simpa only [smul_eq_mul] using h
  calc
    _ = ∑ k ∈ Finset.range (p + 1),
          ((-1 : ℝ) ^ k * ((n + 1).ascFactorial k : ℝ) *
              (p.choose k : ℝ) * x ^ (p - k)) *
            volterraIntegral (n + k) (extendedFabius F) 0 x := h'
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [volterraIntegral_extendedFabius_eq_extendedFabiusPrimitive F hF]

/-- For every `x ≤ 1`, the polynomial-weighted Volterra integral can be
written entirely with the bounded Fabius function.  Negative endpoints are
included: both bounded and signed functions vanish on the intervening
nonpositive interval. -/
theorem volterraIntegral_polynomial_mul_fabiusReal
    (F : BoundedFabius) (hF : IsFabius F)
    (p : Polynomial ℝ) (n : ℕ) {x : ℝ} (hx : x ≤ 1) :
    volterraIntegral n (fun t => p.eval t * fabiusReal F t) 0 x =
      ∑ k ∈ Finset.range (p.natDegree + 1),
        ((-1 : ℝ) ^ k * ((n + 1).ascFactorial k : ℝ) *
            (Polynomial.hasseDeriv k p).eval x) *
          ((2 : ℝ) ^ (n + k + 1).choose 2 *
            fabiusReal F (x / (2 : ℝ) ^ (n + k + 1))) := by
  have hf : IntervalIntegrable (fabiusReal F) volume 0 x :=
    hF.contDiff.continuous.intervalIntegrable 0 x
  have h := volterraIntegral_polynomial_smul p n (fabiusReal F) 0 x hf
  have h' :
      volterraIntegral n (fun t => p.eval t * fabiusReal F t) 0 x =
        ∑ k ∈ Finset.range (p.natDegree + 1),
          ((-1 : ℝ) ^ k * ((n + 1).ascFactorial k : ℝ) *
              (Polynomial.hasseDeriv k p).eval x) *
            volterraIntegral (n + k) (fabiusReal F) 0 x := by
    simpa only [smul_eq_mul] using h
  calc
    _ = ∑ k ∈ Finset.range (p.natDegree + 1),
          ((-1 : ℝ) ^ k * ((n + 1).ascFactorial k : ℝ) *
              (Polynomial.hasseDeriv k p).eval x) *
            volterraIntegral (n + k) (fabiusReal F) 0 x := h'
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [volterraIntegral_fabiusReal_eq_rescaled F hF (n + k) hx]

/-- Monomial specialization of the bounded polynomial formula, valid for
every endpoint `x ≤ 1`. -/
theorem volterraIntegral_pow_mul_fabiusReal
    (F : BoundedFabius) (hF : IsFabius F)
    (p n : ℕ) {x : ℝ} (hx : x ≤ 1) :
    volterraIntegral n (fun t => t ^ p * fabiusReal F t) 0 x =
      ∑ k ∈ Finset.range (p + 1),
        ((-1 : ℝ) ^ k * ((n + 1).ascFactorial k : ℝ) *
            (p.choose k : ℝ) * x ^ (p - k)) *
          ((2 : ℝ) ^ (n + k + 1).choose 2 *
            fabiusReal F (x / (2 : ℝ) ^ (n + k + 1))) := by
  have hf : IntervalIntegrable (fabiusReal F) volume 0 x :=
    hF.contDiff.continuous.intervalIntegrable 0 x
  have h := volterraIntegral_pow_smul p n (fabiusReal F) 0 x hf
  have h' :
      volterraIntegral n (fun t => t ^ p * fabiusReal F t) 0 x =
        ∑ k ∈ Finset.range (p + 1),
          ((-1 : ℝ) ^ k * ((n + 1).ascFactorial k : ℝ) *
              (p.choose k : ℝ) * x ^ (p - k)) *
            volterraIntegral (n + k) (fabiusReal F) 0 x := by
    simpa only [smul_eq_mul] using h
  calc
    _ = ∑ k ∈ Finset.range (p + 1),
          ((-1 : ℝ) ^ k * ((n + 1).ascFactorial k : ℝ) *
              (p.choose k : ℝ) * x ^ (p - k)) *
            volterraIntegral (n + k) (fabiusReal F) 0 x := h'
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [volterraIntegral_fabiusReal_eq_rescaled F hF (n + k) hx]

/-- The cubic ordinary primitive, recorded explicitly as a regression theorem
for the full factorial and dyadic scaling in the finite commutator. -/
theorem integral_cube_mul_fabiusReal_eq
    (F : BoundedFabius) (hF : IsFabius F) {x : ℝ} (hx : x ≤ 1) :
    (∫ t in 0..x, t ^ 3 * fabiusReal F t) =
      x ^ 3 * fabiusReal F (x / 2) -
        6 * x ^ 2 * fabiusReal F (x / 4) +
        48 * x * fabiusReal F (x / 8) -
        384 * fabiusReal F (x / 16) := by
  have h := volterraIntegral_pow_mul_fabiusReal F hF 3 0 hx
  rw [volterraIntegral_zero] at h
  norm_num [Finset.sum_range_succ, Nat.ascFactorial, Nat.choose] at h
  convert h using 1
  ring

end Fabius
