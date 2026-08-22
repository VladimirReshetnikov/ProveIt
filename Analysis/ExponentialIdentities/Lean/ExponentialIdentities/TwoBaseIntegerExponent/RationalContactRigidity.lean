import ExponentialIdentities.TwoBaseIntegerExponent.SparsePowerCurve
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Rational contact rigidity on an irrational power curve

This module isolates the algebraic leading-coefficient mechanism behind the report's
`contact = multiplicity` theorem.  A nonzero rational homogeneous form remains nonzero on
the tangent direction `(a, b * τ)` when `τ` is transcendental.  As a concrete analytic
endpoint, a rational Padé residual `B(t) * t^τ - A(t)` meeting the curve at `t = 1`
has nonzero first derivative whenever `B(1) ≠ 0`.

The full arbitrary-multiplicity Taylor packaging remains in the paper layer; the finite
homogeneous obstruction and the transverse Padé endpoint below are kernel checked.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Polynomial

noncomputable section

/-- A nonzero rational polynomial cannot vanish at a transcendental real number. -/
theorem ratPolynomial_eval₂_ne_zero_of_transcendental {tau : ℝ}
    (htau : Transcendental ℚ tau) {P : Polynomial ℚ} (hP : P ≠ 0) :
    Polynomial.eval₂ (algebraMap ℚ ℝ) tau P ≠ 0 := by
  intro hzero
  apply hP
  apply (transcendental_iff.mp htau P)
  simpa only [Polynomial.aeval_def] using hzero

/-- The univariate polynomial obtained by evaluating a rational homogeneous form of total
degree `s` on the direction `(a, b * T)`. -/
def homogeneousContactPolynomial (s : ℕ) (c : Fin (s + 1) → ℚ) (a b : ℚ) :
    Polynomial ℚ :=
  ∑ j, Polynomial.C (c j * a ^ (s - (j : ℕ)) * b ^ (j : ℕ)) *
    Polynomial.X ^ (j : ℕ)

/-- A nonzero homogeneous rational form remains a nonzero polynomial on every direction
whose two rational coordinates are nonzero. -/
theorem homogeneousContactPolynomial_ne_zero {s : ℕ} {c : Fin (s + 1) → ℚ}
    {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : ∃ j, c j ≠ 0) :
    homogeneousContactPolynomial s c a b ≠ 0 := by
  obtain ⟨j, hj⟩ := hc
  intro hzero
  have hcoeff := congrArg (fun P : Polynomial ℚ ↦ P.coeff (j : ℕ)) hzero
  simp only [homogeneousContactPolynomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hcoeff
  have hjterm : c j * a ^ (s - (j : ℕ)) * b ^ (j : ℕ) = 0 := by
    simpa only [Fin.val_inj, Finset.sum_ite_eq, Finset.mem_univ, if_true] using hcoeff
  exact (mul_ne_zero (mul_ne_zero hj (pow_ne_zero _ ha)) (pow_ne_zero _ hb)) hjterm

/-- **Rational contact leading coefficient.**  A nonzero rational homogeneous form cannot
vanish on the tangent direction `(a, b * tau)` when `tau` is transcendental and `a,b` are
nonzero rationals.  This is the algebraic core of `contact = multiplicity`. -/
theorem homogeneousContactCoefficient_ne_zero {s : ℕ} {tau : ℝ}
    (htau : Transcendental ℚ tau) (c : Fin (s + 1) → ℚ)
    {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : ∃ j, c j ≠ 0) :
    Polynomial.eval₂ (algebraMap ℚ ℝ) tau (homogeneousContactPolynomial s c a b) ≠ 0 :=
  ratPolynomial_eval₂_ne_zero_of_transcendental htau
    (homogeneousContactPolynomial_ne_zero ha hb hc)

/-- The first contact coefficient of a rational Padé residual at `1` cannot vanish when
the coefficient of the irrational exponent is nonzero. -/
theorem rationalPade_firstContactCoefficient_ne_zero {tau : ℝ}
    (htau : Transcendental ℚ tau) (A B : Polynomial ℚ)
    (hB : B.eval (1 : ℚ) ≠ 0) :
    ((B.eval (1 : ℚ) : ℚ) : ℝ) * tau +
        ((B.derivative.eval (1 : ℚ) : ℚ) : ℝ) -
          ((A.derivative.eval (1 : ℚ) : ℚ) : ℝ) ≠ 0 := by
  let P : Polynomial ℚ :=
    Polynomial.C (B.derivative.eval (1 : ℚ) - A.derivative.eval (1 : ℚ)) +
      Polynomial.C (B.eval (1 : ℚ)) * Polynomial.X
  have hP : P ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (fun Q : Polynomial ℚ ↦ Q.coeff 1) hzero
    have : B.eval (1 : ℚ) = 0 := by
      simp only [P, Polynomial.coeff_add, Polynomial.coeff_C,
        Polynomial.coeff_C_mul_X, Polynomial.coeff_zero] at hcoeff
      norm_num at hcoeff
      exact hcoeff
    exact hB this
  have heval := ratPolynomial_eval₂_ne_zero_of_transcendental htau hP
  have hcalc : Polynomial.eval₂ (algebraMap ℚ ℝ) tau P =
      ((B.eval (1 : ℚ) : ℚ) : ℝ) * tau +
        ((B.derivative.eval (1 : ℚ) : ℚ) : ℝ) -
          ((A.derivative.eval (1 : ℚ) : ℚ) : ℝ) := by
    simp only [P, Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_C, map_sub,
      Polynomial.eval₂_mul, Polynomial.eval₂_X]
    change ((B.derivative.eval (1 : ℚ) : ℚ) : ℝ) -
        ((A.derivative.eval (1 : ℚ) : ℚ) : ℝ) +
          ((B.eval (1 : ℚ) : ℚ) : ℝ) * tau = _
    ring
  rwa [hcalc] at heval

/-- Analytic form of the rational first-contact obstruction. -/
theorem hasDerivAt_rationalPadeResidual_one {tau : ℝ}
    (A B : Polynomial ℚ) :
    HasDerivAt
      (fun t : ℝ ↦
        Polynomial.eval t (B.map (algebraMap ℚ ℝ)) * t ^ tau -
          Polynomial.eval t (A.map (algebraMap ℚ ℝ)))
      (((B.eval (1 : ℚ) : ℚ) : ℝ) * tau +
        ((B.derivative.eval (1 : ℚ) : ℚ) : ℝ) -
          ((A.derivative.eval (1 : ℚ) : ℚ) : ℝ))
      1 := by
  have hB := (B.map (algebraMap ℚ ℝ)).hasDerivAt 1
  have hA := (A.map (algebraMap ℚ ℝ)).hasDerivAt 1
  have hr := Real.hasDerivAt_rpow_const (x := (1 : ℝ)) (p := tau) (Or.inl one_ne_zero)
  have hBeval : Polynomial.eval₂ (algebraMap ℚ ℝ) (1 : ℝ) B =
      ((B.eval (1 : ℚ) : ℚ) : ℝ) := by
    simpa using (Polynomial.eval₂_at_apply (algebraMap ℚ ℝ) (1 : ℚ) (p := B))
  have hBderiv : Polynomial.eval₂ (algebraMap ℚ ℝ) (1 : ℝ) B.derivative =
      ((B.derivative.eval (1 : ℚ) : ℚ) : ℝ) := by
    simpa using
      (Polynomial.eval₂_at_apply (algebraMap ℚ ℝ) (1 : ℚ) (p := B.derivative))
  have hAderiv : Polynomial.eval₂ (algebraMap ℚ ℝ) (1 : ℝ) A.derivative =
      ((A.derivative.eval (1 : ℚ) : ℚ) : ℝ) := by
    simpa using
      (Polynomial.eval₂_at_apply (algebraMap ℚ ℝ) (1 : ℚ) (p := A.derivative))
  have hraw := (hB.mul hr).sub hA
  apply hraw.congr_deriv
  simp only [Polynomial.derivative_map, Polynomial.eval_map, Real.one_rpow, mul_one]
  rw [hBeval, hBderiv, hAderiv]
  ring

/-- Hence a rational Padé residual meeting the irrational power graph at `1` is transverse
whenever its denominator does not vanish there. -/
theorem rationalPadeResidual_deriv_ne_zero {tau : ℝ}
    (htau : Transcendental ℚ tau) (A B : Polynomial ℚ)
    (hB : B.eval (1 : ℚ) ≠ 0) :
    HasDerivAt
      (fun t : ℝ ↦
        Polynomial.eval t (B.map (algebraMap ℚ ℝ)) * t ^ tau -
          Polynomial.eval t (A.map (algebraMap ℚ ℝ)))
      (((B.eval (1 : ℚ) : ℚ) : ℝ) * tau +
        ((B.derivative.eval (1 : ℚ) : ℚ) : ℝ) -
          ((A.derivative.eval (1 : ℚ) : ℚ) : ℝ))
      1 ∧
    ((B.eval (1 : ℚ) : ℚ) : ℝ) * tau +
        ((B.derivative.eval (1 : ℚ) : ℚ) : ℝ) -
          ((A.derivative.eval (1 : ℚ) : ℚ) : ℝ) ≠ 0 :=
  ⟨hasDerivAt_rationalPadeResidual_one A B,
    rationalPade_firstContactCoefficient_ne_zero htau A B hB⟩

end

end LeanProofs.TwoBaseIntegerExponent
