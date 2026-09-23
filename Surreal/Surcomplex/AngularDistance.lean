import Surreal.Surcomplex.InverseTrigonometry
import Surreal.Surcomplex.AngleGroup
import Surreal.Surcomplex.Valuation
import Surreal.Foundations.SignSequenceFiniteLeading

/-!
# Angular distance on the actual unit circle

Inverse cosine defines the least unsigned angle between two actual unit
directions. The half-angle identity and Jordan bounds give the chordal
comparison and exact valuation equality in `trigonometry:thm:metric`,
`trigonometry:eq:metricbounds` and `trigonometry:eq:metricval`.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- The real coordinate of an actual unit direction belongs to the closed unit interval. -/
theorem unitCircle_re_mem (z : UnitCircle.{u}) : z.val.re ∈ Set.Icc (-1) 1 := by
  have h := abs_re_le_modulus z.val
  rw [modulus_unitCircle] at h
  exact abs_le.mp h

/-- The unsigned angle of a unit direction, in the actual interval `[0, pi]`. -/
def unitCircleAngle (z : UnitCircle.{u}) : SignSequence.FiniteElement.{u} :=
  arccos ⟨z.val.re, unitCircle_re_mem z⟩

theorem unitCircleAngle_mem (z : UnitCircle.{u}) :
    (unitCircleAngle z).val ∈ Set.Icc 0 (SignSequence.ofReal Real.pi) := arccos_mem _

@[simp] theorem finiteCos_unitCircleAngle (z : UnitCircle.{u}) :
    finiteCos (unitCircleAngle z) = z.val.re := finiteCos_arccos _

/-- The angular distance uses the actual relative unit direction. -/
def angularDistance (z w : UnitCircle.{u}) : SignSequence.{u} :=
  (unitCircleAngle (z⁻¹ * w)).val

/-- The source formula for the relative direction is conjugate multiplication. -/
theorem coe_unitCircle_relative (z w : UnitCircle.{u}) :
    (z⁻¹ * w).val = conj z.val * w.val := rfl

theorem angularDistance_nonneg (z w : UnitCircle.{u}) : 0 ≤ angularDistance z w :=
  (unitCircleAngle_mem _).1

theorem angularDistance_le_pi (z w : UnitCircle.{u}) :
    angularDistance z w ≤ SignSequence.ofReal Real.pi := (unitCircleAngle_mem _).2

/-- Squared chord length is twice the real-coordinate defect of the relative direction. -/
theorem modulus_unitCircle_sub_sq (z w : UnitCircle.{u}) :
    modulus (z.val - w.val) ^ 2 = 2 - 2 * (z⁻¹ * w).val.re := by
  have hz := modulus_sq z.val
  have hw := modulus_sq w.val
  rw [modulus_unitCircle, one_pow, normSq_eq] at hz hw
  rw [modulus_sq, normSq_eq, coe_unitCircle_relative]
  simp only [mul_re, conj_re, conj_im]
  change (z.val.re - w.val.re) ^ 2 + (z.val.im - w.val.im) ^ 2 =
    2 - 2 * (z.val.re * w.val.re - -z.val.im * w.val.im)
  nlinarith only [hz, hw]

private theorem half_unitCircleAngle_mem (z : UnitCircle.{u}) :
    (finiteHalf (unitCircleAngle z)).val ∈ Set.Icc 0 (SignSequence.ofReal (Real.pi / 2)) := by
  have h := unitCircleAngle_mem z
  rw [val_finiteHalf, map_div₀, map_ofNat]
  exact ⟨div_nonneg h.1 (by norm_num), (div_le_div_iff_of_pos_right (by norm_num)).mpr h.2⟩

/-- The exact chord formula holds at every scale and includes coincident and antipodal points. -/
theorem modulus_unitCircle_sub_eq_two_sin (z w : UnitCircle.{u}) :
    modulus (z.val - w.val) = 2 * finiteSin (finiteHalf (unitCircleAngle (z⁻¹ * w))) := by
  have hj := finiteSin_jordan _ (half_unitCircleAngle_mem (z⁻¹ * w))
  have hsin : 0 ≤ finiteSin (finiteHalf (unitCircleAngle (z⁻¹ * w))) :=
    (div_nonneg (mul_nonneg (by norm_num) (half_unitCircleAngle_mem _).1)
      (by simpa only [map_zero] using SignSequence.ofReal_strictMono.monotone Real.pi_pos.le)).trans hj.1
  apply (sq_eq_sq₀ (modulus_nonneg _) (mul_nonneg (by norm_num) hsin)).mp
  rw [modulus_unitCircle_sub_sq]
  have hs := finiteSin_finiteHalf_sq (unitCircleAngle (z⁻¹ * w))
  rw [finiteCos_unitCircleAngle] at hs
  nlinarith only [hs]

/-- Chord length and angular distance differ by at most the ordinary factor `pi/2`. -/
theorem angularDistance_chord_bounds (z w : UnitCircle.{u}) :
    modulus (z.val - w.val) ≤ angularDistance z w ∧
      angularDistance z w ≤ SignSequence.ofReal (Real.pi / 2) * modulus (z.val - w.val) := by
  have hj := finiteSin_jordan _ (half_unitCircleAngle_mem (z⁻¹ * w))
  rw [val_finiteHalf] at hj
  have hp : (0 : SignSequence.{u}) < SignSequence.ofReal Real.pi := by
    simpa only [map_zero] using SignSequence.ofReal_strictMono Real.pi_pos
  have hlo := (div_le_iff₀ hp).mp hj.1
  rw [modulus_unitCircle_sub_eq_two_sin, map_div₀, map_ofNat]
  change 2 * finiteSin _ ≤ (unitCircleAngle (z⁻¹ * w)).val ∧
    (unitCircleAngle (z⁻¹ * w)).val ≤ _
  constructor <;> nlinarith only [hj.2, hlo]

/-- Angular distance has exactly the chord's valuation, with zero included. -/
theorem valuation_angularDistance (z w : UnitCircle.{u}) :
    SignSequence.valuation (angularDistance z w) = valuation (z.val - w.val) := by
  obtain ⟨hlo, hhi⟩ := angularDistance_chord_bounds z w
  apply le_antisymm
  · exact SignSequence.valuation_antitone_nonneg (modulus_nonneg _) hlo
  · have h := SignSequence.valuation_antitone_nonneg (angularDistance_nonneg z w) hhi
    rw [SignSequence.valuation_mul,
      SignSequence.valuation_ofReal_of_ne_zero (ne_of_gt (half_pos Real.pi_pos)), zero_add] at h
    exact h

end
end Surreal.Surcomplex
