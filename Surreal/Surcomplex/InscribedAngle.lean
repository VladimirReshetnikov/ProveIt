import Surreal.Surcomplex.CircleChordQuotient
import Surreal.Surcomplex.LineAngle

/-!
# The actual directed inscribed-angle theorem

The directed clause of `trigonometry:prop:inscribed` is an equality in the
quotient of finite actual surreal angles by ordinary integral multiples
of `pi`. The central angle lives modulo `2*pi`, and the proved halving
equivalence makes the statement independent of every choice of lift.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- The directed angle between two nonzero vectors, modulo ordinary full turns. -/
def directedAngleBetween (z w : Surcomplex.{u}) (hz : z ≠ 0) (hw : w ≠ 0) :
    Multiplicative SignSequence.FiniteElement.{u} ⧸ anglePeriods :=
  angleQuotientEquiv.symm (unitDirection (Units.mk0 w hw / Units.mk0 z hz))

/-- The directed angle between two nonzero vectors, modulo ordinary half turns. -/
def directedLineAngleBetween (z w : Surcomplex.{u}) (hz : z ≠ 0) (hw : w ≠ 0) :
    LineAngle.{u} :=
  directedLineAngle (Units.mk0 w hw / Units.mk0 z hz)

/-- A unit phase quotient identifies the directed full-turn angle class. -/
theorem directedAngleBetween_eq_of_phase_quotient (z w : Surcomplex.{u})
    (hz : z ≠ 0) (hw : w ≠ 0) (θ : SignSequence.FiniteElement.{u})
    (hq : w / z = finitePhase θ) :
    directedAngleBetween z w hz hw = QuotientGroup.mk (Multiplicative.ofAdd θ) := by
  apply angleQuotientEquiv.injective
  rw [directedAngleBetween, MulEquiv.apply_symm_apply, angleQuotientEquiv_mk]
  apply Subtype.ext
  rw [coe_unitDirection]
  change w / z / ofReal (modulus (w / z)) = finitePhase θ
  rw [hq, modulus_finitePhase, map_one, div_one]

/-- A real phase quotient identifies the directed half-turn angle class, regardless of sign. -/
theorem directedLineAngleBetween_eq_of_real_phase_quotient (z w : Surcomplex.{u})
    (hz : z ≠ 0) (hw : w ≠ 0) (r : SignSequence.{u}) (θ : SignSequence.FiniteElement.{u})
    (hq : w / z = ofReal r * finitePhase θ) :
    directedLineAngleBetween z w hz hw = lineAngle θ :=
  directedLineAngle_eq_of_real_phase (Units.mk0 w hw / Units.mk0 z hz) r θ hq

/-- The central angle of two circle parameters is their full difference modulo a full turn. -/
theorem circle_central_directedAngle (O : Surcomplex.{u}) (R : SignSequence.{u})
    (hR : R ≠ 0) (θ₁ θ₂ : SignSequence.FiniteElement.{u}) :
    directedAngleBetween (circlePoint O R θ₁ - O) (circlePoint O R θ₂ - O)
      (sub_ne_zero.mpr (circlePoint_ne_center O R hR θ₁))
      (sub_ne_zero.mpr (circlePoint_ne_center O R hR θ₂)) =
        QuotientGroup.mk (Multiplicative.ofAdd (θ₂ - θ₁)) :=
  directedAngleBetween_eq_of_phase_quotient _ _ _ _ _
    (circle_central_quotient O R θ₁ θ₂ hR)

/-- The two chords have half the central parameter difference as directed line angle. -/
theorem circle_inscribed_directedLineAngle (O : Surcomplex.{u}) (R : SignSequence.{u})
    (hR : R ≠ 0) (θ₁ θ₂ θ₃ : SignSequence.FiniteElement.{u})
    (h13 : circlePoint O R θ₁ ≠ circlePoint O R θ₃)
    (h23 : circlePoint O R θ₂ ≠ circlePoint O R θ₃) :
    directedLineAngleBetween (circlePoint O R θ₁ - circlePoint O R θ₃)
      (circlePoint O R θ₂ - circlePoint O R θ₃)
      (sub_ne_zero.mpr h13) (sub_ne_zero.mpr h23) = lineAngle (finiteHalf (θ₂ - θ₁)) :=
  directedLineAngleBetween_eq_of_real_phase_quotient _ _ _ _ _ _
    (circle_chord_quotient O R θ₁ θ₂ θ₃ hR h13)

/-- A point on a positive-radius circle has a nonzero central vector. -/
theorem sub_center_ne_zero_of_mem_circle (O : Surcomplex.{u}) (R : SignSequence.{u})
    (hR : 0 < R) (z : Surcomplex.{u}) (hz : modulus (z - O) = R) : z - O ≠ 0 := by
  apply (modulus_eq_zero_iff _).not.mp
  rw [hz]
  exact hR.ne'

/-- The directed inscribed angle is half the directed central angle on any actual circle. -/
theorem inscribed_angle (O : Surcomplex.{u}) (R : SignSequence.{u}) (hR : 0 < R)
    (z₁ z₂ z₃ : Surcomplex.{u})
    (h₁ : modulus (z₁ - O) = R) (h₂ : modulus (z₂ - O) = R)
    (h₃ : modulus (z₃ - O) = R) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃) :
    directedLineAngleBetween (z₁ - z₃) (z₂ - z₃)
      (sub_ne_zero.mpr h13) (sub_ne_zero.mpr h23) =
        halveAngleQuotient (directedAngleBetween (z₁ - O) (z₂ - O)
          (sub_center_ne_zero_of_mem_circle O R hR z₁ h₁)
          (sub_center_ne_zero_of_mem_circle O R hR z₂ h₂)) := by
  obtain ⟨θ₁, rfl⟩ := (mem_circle_iff_exists_circlePoint O R hR z₁).mp h₁
  obtain ⟨θ₂, rfl⟩ := (mem_circle_iff_exists_circlePoint O R hR z₂).mp h₂
  obtain ⟨θ₃, rfl⟩ := (mem_circle_iff_exists_circlePoint O R hR z₃).mp h₃
  rw [circle_central_directedAngle O R hR.ne', halveAngleQuotient_mk]
  exact circle_inscribed_directedLineAngle O R hR.ne' θ₁ θ₂ θ₃ h13 h23

end
end Surreal.Surcomplex
