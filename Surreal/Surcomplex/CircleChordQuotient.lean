import Surreal.Surcomplex.CircleChords

/-!
# The relative phase of two circle chords

Dividing the two signed chord factorizations cancels their common radius
and imaginary factor. The remaining phase is half the central parameter
difference, times a real scalar. This is the algebraic core of
`trigonometry:prop:inscribed`.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- Every actual finite phase is nonzero because its modulus is one. -/
theorem finitePhase_ne_zero (θ : SignSequence.FiniteElement.{u}) : finitePhase θ ≠ 0 := by
  apply (modulus_eq_zero_iff _).not.mp
  rw [modulus_finitePhase]
  exact one_ne_zero

/-- A nonzero-radius circle never contains its center. -/
theorem circlePoint_ne_center (O : Surcomplex.{u}) (R : SignSequence.{u}) (hR : R ≠ 0)
    (θ : SignSequence.FiniteElement.{u}) : circlePoint O R θ ≠ O := by
  intro he
  have h := congrArg (fun z : Surcomplex.{u} => z - O) he
  simp only [circlePoint, add_sub_cancel_left, sub_self] at h
  exact (mul_ne_zero ((map_ne_zero ofReal).mpr hR) (finitePhase_ne_zero θ)) h

/-- Distinct circle endpoints have a nonzero signed half-difference sine. -/
theorem sin_half_sub_ne_zero_of_circlePoint_ne (O : Surcomplex.{u}) (R : SignSequence.{u})
    (θ φ : SignSequence.FiniteElement.{u}) (h : circlePoint O R θ ≠ circlePoint O R φ) :
    finiteSin (finiteHalf (θ - φ)) ≠ 0 := by
  intro hs
  apply h
  apply sub_eq_zero.mp
  rw [circlePoint_sub_factor, hs, mul_zero, map_zero, zero_mul, zero_mul]

/-- The quotient of two nonzero-based circle chords has half the central phase modulo a real sign. -/
theorem circle_chord_quotient (O : Surcomplex.{u}) (R : SignSequence.{u})
    (θ₁ θ₂ θ₃ : SignSequence.FiniteElement.{u}) (hR : R ≠ 0)
    (h13 : circlePoint O R θ₁ ≠ circlePoint O R θ₃) :
    (circlePoint O R θ₂ - circlePoint O R θ₃) /
      (circlePoint O R θ₁ - circlePoint O R θ₃) =
      ofReal (finiteSin (finiteHalf (θ₂ - θ₃)) / finiteSin (finiteHalf (θ₁ - θ₃))) *
        finitePhase (finiteHalf (θ₂ - θ₁)) := by
  have hs := sin_half_sub_ne_zero_of_circlePoint_ne O R θ₁ θ₃ h13
  have hI : (I : Surcomplex.{u}) ≠ 0 := by
    apply (modulus_eq_zero_iff _).not.mp
    rw [modulus_I]
    exact one_ne_zero
  have hh : finiteHalf (θ₂ - θ₁) =
      finiteHalf (θ₃ + θ₂) - finiteHalf (θ₃ + θ₁) := by
    apply ArchimedeanClass.FiniteElement.ext
    simp only [val_finiteHalf, ArchimedeanClass.FiniteElement.val_sub,
      ArchimedeanClass.FiniteElement.val_add]
    ring
  rw [circlePoint_sub_factor, circlePoint_sub_factor, hh, finitePhase_sub]
  simp only [map_mul, map_div₀, map_ofNat]
  field_simp [((map_ne_zero ofReal).mpr hR), ((map_ne_zero ofReal).mpr hs), hI,
    finitePhase_ne_zero (finiteHalf (θ₃ + θ₁))]

/-- The central quotient is exactly the phase of the full parameter difference. -/
theorem circle_central_quotient (O : Surcomplex.{u}) (R : SignSequence.{u})
    (θ₁ θ₂ : SignSequence.FiniteElement.{u}) (hR : R ≠ 0) :
    (circlePoint O R θ₂ - O) / (circlePoint O R θ₁ - O) = finitePhase (θ₂ - θ₁) := by
  simp only [circlePoint, add_sub_cancel_left, finitePhase_sub]
  exact mul_div_mul_left _ _ ((map_ne_zero ofReal).mpr hR)

end
end Surreal.Surcomplex
