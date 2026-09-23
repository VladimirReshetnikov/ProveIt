import Surreal.Surcomplex.AmplitudePhase
import Surreal.Surcomplex.LineCircleIntersection

/-!
# Differential classification of first-harmonic intersections

This joins the angular and algebraic parts of `trigonometry:thm:amplitude`.
The first and second angular derivatives are fine derivatives of the actual
functions. The Jacobian is the determinant of the circle and line gradients.
In particular, the endpoint solution has quadratic contact, including when
the normal vector is infinite or infinitesimal.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- The source's nonzero normal-vector hypothesis is precisely positive squared amplitude. -/
theorem normal_sq_pos_iff (A B : SignSequence.{u}) :
    0 < A ^ 2 + B ^ 2 ↔ A ≠ 0 ∨ B ≠ 0 := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    simp only [hn.1, hn.2, zero_pow (by decide : 2 ≠ 0), add_zero, lt_self_iff_false] at h
  · rintro (h | h)
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h) (sq_nonneg B)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg A) (sq_pos_of_ne_zero h)

/-- An angular solution is an actual intersection of the stated line with the unit circle. -/
theorem isLineCircleIntersection_finitePhase_iff (A B D : SignSequence.{u})
    (θ : SignSequence.FiniteElement.{u}) :
    IsLineCircleIntersection A B D (finitePhase θ) ↔
      A * finiteCos θ + B * finiteSin θ = D := by
  change (modulus (finitePhase θ) = 1 ∧ _) ↔ _
  simp only [modulus_finitePhase, true_and, finiteCos, finiteSin]

/-- The simple-root derivative magnitude is the square root of the discriminant. -/
theorem firstHarmonic_derivative_abs (A B D : SignSequence.{u})
    (θ : SignSequence.FiniteElement.{u}) (hθ : A * finiteCos θ + B * finiteSin θ = D) :
    |B * finiteCos θ - A * finiteSin θ| =
      SignSequence.sqrt (lineCircleDiscriminant A B D) :=
  abs_lineCircle_angularDerivative ((isLineCircleIntersection_finitePhase_iff A B D θ).mpr hθ)

/-- A positive discriminant makes each angular solution simple. -/
theorem firstHarmonic_derivative_ne_zero (A B D : SignSequence.{u})
    (θ : SignSequence.FiniteElement.{u}) (hθ : A * finiteCos θ + B * finiteSin θ = D)
    (hΔ : 0 < lineCircleDiscriminant A B D) :
    B * finiteCos θ - A * finiteSin θ ≠ 0 := by
  intro he
  have ha := firstHarmonic_derivative_abs A B D θ hθ
  rw [he, abs_zero] at ha
  exact (SignSequence.sqrt_pos hΔ).ne' ha.symm

/-- The two gradient rows have the asserted determinant magnitude at either solution. -/
theorem firstHarmonic_jacobian_abs (A B D : SignSequence.{u})
    (θ : SignSequence.FiniteElement.{u}) (hθ : A * finiteCos θ + B * finiteSin θ = D) :
    |2 * finiteCos θ * B - 2 * finiteSin θ * A| =
      2 * SignSequence.sqrt (lineCircleDiscriminant A B D) :=
  abs_lineCircle_jacobian ((isLineCircleIntersection_finitePhase_iff A B D θ).mpr hθ)

/-- At either amplitude endpoint, the first derivative is zero and the second is `-D ≠ 0`. -/
theorem firstHarmonic_tangent_derivatives (A B D : SignSequence.{u})
    (h : 0 < A ^ 2 + B ^ 2) (hD : |D| = SignSequence.sqrt (A ^ 2 + B ^ 2))
    (θ : SignSequence.FiniteElement.{u}) (hθ : A * finiteCos θ + B * finiteSin θ = D) :
    FineHasDerivAt (fun x => A * cosFunction x + B * sinFunction x) 0 θ.val ∧
      FineHasDerivAt (fun x => B * cosFunction x - A * sinFunction x) (-D) θ.val ∧
      -D ≠ 0 := by
  have hΔ : lineCircleDiscriminant A B D = 0 := by
    have hs := SignSequence.sqrt_sq h.le
    rw [← hD, sq_abs] at hs
    exact sub_eq_zero.mpr hs.symm
  have hz := (isLineCircleIntersection_finitePhase_iff A B D θ).mpr hθ
  have hfirst := lineCircle_angularDerivative_eq_zero hz hΔ
  change B * finiteCos θ - A * finiteSin θ = 0 at hfirst
  have hsecond := lineCircle_secondDerivative_ne_zero h hz hΔ
  refine ⟨?_, ?_, hsecond.2⟩
  · simpa only [hfirst] using fineHasDerivAt_firstHarmonic A B θ
  · simpa only [hθ] using fineHasDerivAt_firstHarmonic_derivative A B θ

/-- The degenerate zero normal gives every class for `D=0`, and none otherwise. -/
theorem zero_normal_solution_iff (D : SignSequence.{u}) (θ : FiniteAngleClass.{u}) :
    angleClassHarmonic 0 0 θ = D ↔ D = 0 := by
  simp only [angleClassHarmonic, zero_mul, zero_add, eq_comm]

end
end Surreal.Surcomplex
