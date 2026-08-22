import Mathlib.RingTheory.Polynomial.Resultant.Basic

open Polynomial

namespace LeanProofs.TwoBaseIntegerExponent

noncomputable section

/-!
# Exact denominator-cancellation counterexample

This module checks the smallest square-grid instance of the report's paired
residual construction at the synthetic favorable pair `(M, A) = (9, 2)`.
The interpolation denominator is `60`, while the cross resultant is coprime
to `60`.  Consequently, grid-denominator divisibility alone cannot yield an
all-prime lower bound for the cross resultant.  The pair is test data, not a
common-exponent solution.
-/

/-- Scaling both degree-indexed resultant inputs by the same scalar contributes
the expected `d^(2*n)`.  No integrality or degree hypothesis is needed because
the two explicit Sylvester size parameters are both `n`. -/
theorem resultant_simultaneous_C_mul
    {R : Type*} [CommRing R] (d : R) (U V : R[X]) (n : ℕ) :
    (C d * U).resultant (C d * V) n n =
      d ^ (2 * n) * U.resultant V n n := by
  rw [resultant_C_mul_left, resultant_C_mul_right, ← mul_assoc, ← pow_add]
  congr 2
  omega

/-- Explicit size-one Sylvester determinant. -/
theorem resultant_linear
    {R : Type*} [CommRing R] (a b c d : R) :
    (C a * X + C b).resultant (C c * X + C d) 1 1 =
      a * d - b * c := by
  unfold Polynomial.resultant
  rw [Matrix.det_fin_two]
  simp [Polynomial.sylvester]
  change d * a - b * c = a * d - b * c
  ring

namespace DenominatorCancellationExample

def P : ℤ[X] :=
  C 127 * X ^ 3 - C 1212 * X ^ 2 + C 3227 * X - C 2082

def Q : ℚ[X] :=
  C (127 / 60) * X ^ 3 - C (101 / 5) * X ^ 2 +
    C (3227 / 60) * X - C (347 / 10)

def F : ℤ[X] := C 5552 - C 127 * X

def G : ℤ[X] := C 3175 * X + C 1041

theorem P_eval_one : eval 1 P = 60 := by norm_num [P]
theorem P_eval_three : eval 3 P = 120 := by norm_num [P]
theorem P_eval_two : eval 2 P = 540 := by norm_num [P]
theorem P_eval_six : eval 6 P = 1080 := by norm_num [P]

theorem Q_eval_one : eval 1 Q = 1 := by norm_num [Q]
theorem Q_eval_three : eval 3 Q = 2 := by norm_num [Q]
theorem Q_eval_two : eval 2 Q = 9 := by norm_num [Q]
theorem Q_eval_six : eval 6 Q = 18 := by norm_num [Q]

theorem Q_coeff_three : Q.coeff 3 = 127 / 60 := by norm_num [Q]

/-- The leading coefficient alone has reduced denominator `60`. -/
theorem Q_coeff_three_den : (Q.coeff 3).den = 60 := by
  rw [Q_coeff_three]
  norm_num

/-- The denominator `60` clears every coefficient and gives the displayed
integral interpolant.  Together with `Q_coeff_three_den`, this certifies that
`60` is the least positive common coefficient denominator. -/
theorem sixty_mul_Q_eq_P :
    C (60 : ℚ) * Q = P.map (Int.castRingHom ℚ) := by
  ext k
  by_cases h0 : k = 0 <;> by_cases h1 : k = 1 <;>
    by_cases h2 : k = 2 <;> by_cases h3 : k = 3 <;>
    simp [Q, P, coeff_X, coeff_C, h0, h1, h2, h3] <;> norm_num ;
    (cases k <;> simp_all)

theorem dyadic_defect_factorization : P.comp (C 2 * X) - C 9 * P =
    (X - C 1) * (X - C 3) * F := by
  simp [P, F]
  ring

theorem triadic_defect_factorization : P.comp (C 3 * X) - C 2 * P =
    (X - C 1) * (X - C 2) * G := by
  simp [P, G]
  ring

theorem cross_resultant_eq : F.resultant G 1 1 = -17759807 := by
  rw [show F = C (-127) * X + C 5552 by simp [F]; ring]
  rw [show G = C 3175 * X + C 1041 by simp [G]]
  rw [resultant_linear]
  norm_num

theorem delta_coprime_cross_resultant :
    IsCoprime (60 : ℤ) (F.resultant G 1 1) := by
  rw [cross_resultant_eq]
  rw [Int.isCoprime_iff_gcd_eq_one]
  norm_num

def U : ℚ[X] := C (1 / 60) * F.map (Int.castRingHom ℚ)

def V : ℚ[X] := C (1 / 60) * G.map (Int.castRingHom ℚ)

/-- The rational residual resultant has the full `60^2` denominator.  Thus the
formal scalar factor from clearing denominators is cancelled exactly. -/
theorem rational_residual_resultant_eq :
    U.resultant V 1 1 = (-17759807 : ℚ) / 3600 := by
  rw [U, V, resultant_simultaneous_C_mul]
  rw [resultant_map_map, cross_resultant_eq]
  norm_num

end DenominatorCancellationExample

end

end LeanProofs.TwoBaseIntegerExponent
