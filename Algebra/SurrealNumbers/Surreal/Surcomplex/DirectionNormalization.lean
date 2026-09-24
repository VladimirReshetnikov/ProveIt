import Surreal.Surcomplex.PolarGroup
import Surreal.Surcomplex.LocalAngularDistance
import Surreal.Surcomplex.ExpLogConjugation

/-!
# Unit directions and the imaginary part of the local logarithm

Extract the unit direction using the already constructed polar group
isomorphism. Removing the positive radial factor leaves the imaginary
part of the strong logarithm unchanged. This supplies the geometric
identification required in `trigonometry:cor:directionstability`.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- The unit-direction projection of the actual multiplicative polar decomposition. -/
def unitDirection : Surcomplex.{u}ˣ →* UnitCircle.{u} where
  toFun z := (polarGroupEquiv.symm z).2
  map_one' := by simp
  map_mul' z w := by simp

@[simp] theorem coe_unitDirection (z : Surcomplex.{u}ˣ) :
    (unitDirection z).val = (z : Surcomplex.{u}) / ofReal (modulus z) :=
  polarGroupEquiv_symm_snd z

/-- The extracted positive radius and direction reconstruct the original nonzero element. -/
theorem modulus_mul_unitDirection (z : Surcomplex.{u}ˣ) :
    ofReal (modulus z) * (unitDirection z).val = z := by
  rw [coe_unitDirection]
  field_simp [(map_ne_zero ofReal).mpr (modulus_pos z.ne_zero).ne']

private theorem finite_of_near_one (z : Surcomplex.{u}) (hi : IsInfinitesimal (z - 1)) :
    IsFinite z := by
  have h := finiteSubring.add_mem (show IsFinite (1 : Surcomplex.{u}) from finiteSubring.one_mem)
    (finite_of_infinitesimal hi)
  simpa only [add_sub_cancel, mem_finiteSubring] using h

private theorem standardPart_of_near_one (z : Surcomplex.{u}) (hi : IsInfinitesimal (z - 1)) :
    standardPart z = 1 := by
  apply (infinitesimal_sub_ofComplex_iff (finite_of_near_one z hi)).mp
  simpa only [map_one] using hi

private theorem standardPart_real_modulus (z : Surcomplex.{u}) (hf : IsFinite z)
    (hs : standardPart z = 1) : standardPart (ofReal (modulus z)) = 1 := by
  have hr : SignSequence.standardPart (modulus z) = 1 := by
    rw [standardPart_modulus hf, hs, norm_one]
  apply Complex.ext
  · simpa only [standardPart_re, ofReal_re, Complex.one_re] using hr
  · simp only [standardPart_im, ofReal_im, SignSequence.standardPart_zero, Complex.one_im]

/-- Normalizing a unit near one preserves its standard part one. -/
theorem standardPart_unitDirection_of_near_one (z : Surcomplex.{u}ˣ)
    (hi : IsInfinitesimal ((z : Surcomplex.{u}) - 1)) :
    standardPart (unitDirection z).val = 1 := by
  have hf := finite_of_near_one (z : Surcomplex.{u}) hi
  have hs := standardPart_of_near_one (z : Surcomplex.{u}) hi
  have hfr : IsFinite (ofReal (modulus z)) :=
    ⟨(isFinite_iff_modulus _).mp hf, SignSequence.finite_zero⟩
  have he := congrArg standardPart (modulus_mul_unitDirection z)
  rw [standardPart_mul hfr (isFinite_unitCircle _), standardPart_real_modulus _ hf hs,
    hs, one_mul] at he
  exact he

/-- The normalized direction of a unit near one is itself near one. -/
theorem infinitesimal_unitDirection_sub_one (z : Surcomplex.{u}ˣ)
    (hi : IsInfinitesimal ((z : Surcomplex.{u}) - 1)) :
    IsInfinitesimal ((unitDirection z).val - 1) := by
  have h := infinitesimal_sub_standardPart (isFinite_unitCircle (unitDirection z))
  simpa only [standardPart_unitDirection_of_near_one z hi, map_one] using h

private theorem infLog_real_im (r : SignSequence.{u}) (hi : IsInfinitesimal (ofReal r - 1)) :
    (infLog (ofReal r - 1) hi).im = 0 := by
  have h := infLog_conj (ofReal r - 1) hi
  have he : conj (ofReal r - 1) = ofReal r - 1 := by simp
  simp only [he] at h
  have hm := congrArg (fun x : Surcomplex.{u} => x.im) h
  rw [conj_im] at hm
  linarith only [hm]

/-- Removing the radial factor does not change the imaginary local logarithm. -/
theorem infLog_unitDirection_im (z : Surcomplex.{u}ˣ)
    (hi : IsInfinitesimal ((z : Surcomplex.{u}) - 1)) :
    (infLog ((unitDirection z).val - 1) (infinitesimal_unitDirection_sub_one z hi)).im =
      (infLog ((z : Surcomplex.{u}) - 1) hi).im := by
  have hf := finite_of_near_one (z : Surcomplex.{u}) hi
  have hs := standardPart_of_near_one (z : Surcomplex.{u}) hi
  have hfr : IsFinite (ofReal (modulus z)) :=
    ⟨(isFinite_iff_modulus _).mp hf, SignSequence.finite_zero⟩
  have hir : IsInfinitesimal (ofReal (modulus z) - 1) := by
    simpa only [standardPart_real_modulus _ hf hs, map_one] using infinitesimal_sub_standardPart hfr
  have h := infLog_mul (ofReal (modulus z) - 1) ((unitDirection z).val - 1)
    hir (infinitesimal_unitDirection_sub_one z hi)
  simp only [add_sub_cancel, modulus_mul_unitDirection] at h
  have hm := congrArg (fun x : Surcomplex.{u} => x.im) h
  change (infLog ((z : Surcomplex.{u}) - 1) hi).im =
    (infLog (ofReal (modulus z) - 1) hir).im +
      (infLog ((unitDirection z).val - 1) (infinitesimal_unitDirection_sub_one z hi)).im at hm
  rw [infLog_real_im, zero_add] at hm
  exact hm.symm

/-- Unit directions of relatively infinitesimally separated elements have the same standard part. -/
theorem unitDirection_standardPart_eq_of_relative (z w : Surcomplex.{u}ˣ)
    (hi : IsInfinitesimal (((w / z : Surcomplex.{u}ˣ) : Surcomplex.{u}) - 1)) :
    standardPart (unitDirection z).val = standardPart (unitDirection w).val := by
  have he : circleStandardPart (unitDirection (w / z)) = 1 :=
    Circle.ext (standardPart_unitDirection_of_near_one _ hi)
  rw [map_div, map_div, div_eq_one] at he
  exact congrArg (fun c : Circle => (c : ℂ)) he.symm

/-- The actual local angle of two nonzero directions is the imaginary relative logarithm. -/
theorem localAngle_unitDirection_eq_infLog_im (z w : Surcomplex.{u}ˣ)
    (hi : IsInfinitesimal (((w / z : Surcomplex.{u}ˣ) : Surcomplex.{u}) - 1)) :
    (localAngle (unitDirection z) (unitDirection w)).val =
      (infLog (((w / z : Surcomplex.{u}ˣ) : Surcomplex.{u}) - 1) hi).im := by
  have ha := ofReal_localAngle_eq_log (unitDirection z) (unitDirection w)
    (unitDirection_standardPart_eq_of_relative z w hi)
  have hr := congrArg (fun x : Surcomplex.{u} => x.re) ha
  have hq : (unitDirection (w / z)).val =
      (unitDirection w).val / (unitDirection z).val := by
    rw [map_div, Unitary.coe_div]
  have he := infLog_unitDirection_im (w / z) hi
  simp only [hq] at he
  have hr' : (localAngle (unitDirection z) (unitDirection w)).val =
      (infLog ((unitDirection w).val / (unitDirection z).val - 1)
        (infinitesimal_relative_sub_one _ _ (unitDirection_standardPart_eq_of_relative z w hi))).im := by
    simpa using hr
  exact hr'.trans he

end
end Surreal.Surcomplex
