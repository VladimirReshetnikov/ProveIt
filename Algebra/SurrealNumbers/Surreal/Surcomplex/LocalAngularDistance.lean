import Surreal.Surcomplex.AngularMetric
import Surreal.Surcomplex.CircleSplitting

/-!
# The infinitesimal logarithmic angle between nearby directions

For two unit directions with the same standard part, their relative phase
has a unique infinitesimal real angle. Its absolute value is angular
distance, and its logarithmic formula and valuation give
`trigonometry:eq:localangle`.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- The infinitesimal coordinate of the relative direction in the canonical circle splitting. -/
def localAngle (z w : UnitCircle.{u}) : SignSequence.infinitesimalAddSubgroup.{u} :=
  (circleSplit (z⁻¹ * w)).2.toAdd

private theorem relative_standardPart_eq_one (z w : UnitCircle.{u})
    (h : standardPart z.val = standardPart w.val) : circleStandardPart (z⁻¹ * w) = 1 := by
  have he : circleStandardPart z = circleStandardPart w := Circle.ext h
  rw [map_mul, map_inv, he, inv_mul_cancel]

/-- Equal-residue directions differ by the phase of the canonical infinitesimal angle. -/
theorem finitePhase_localAngle (z w : UnitCircle.{u})
    (h : standardPart z.val = standardPart w.val) :
    finitePhase (infinitesimalFiniteAngle (localAngle z w)) = (z⁻¹ * w).val := by
  have he := circleSplit.symm_apply_apply (z⁻¹ * w)
  rw [circleSplit_symm_apply] at he
  change circleOfComplex (circleSplit (z⁻¹ * w)).1 *
    circleInfinitesimalPhase (circleSplit (z⁻¹ * w)).2 = z⁻¹ * w at he
  rw [circleSplit_fst, relative_standardPart_eq_one z w h, map_one, one_mul] at he
  exact congrArg (fun r : UnitCircle.{u} => r.val) he

/-- The oriented infinitesimal relative angle is unique. -/
theorem existsUnique_infinitesimal_relative_angle (z w : UnitCircle.{u})
    (h : standardPart z.val = standardPart w.val) :
    ∃! δ : SignSequence.infinitesimalAddSubgroup.{u},
      finitePhase (infinitesimalFiniteAngle δ) = (z⁻¹ * w).val := by
  refine ⟨localAngle z w, finitePhase_localAngle z w h, ?_⟩
  intro δ hδ
  have he : circleInfinitesimalPhase (Multiplicative.ofAdd δ) =
      circleInfinitesimalPhase (Multiplicative.ofAdd (localAngle z w)) :=
    Subtype.ext (hδ.trans (finitePhase_localAngle z w h).symm)
  exact congrArg Multiplicative.toAdd (circleInfinitesimalPhase_injective he)

/-- For equal-residue directions the angular distance is the absolute infinitesimal angle. -/
theorem angularDistance_eq_abs_localAngle (z w : UnitCircle.{u})
    (h : standardPart z.val = standardPart w.val) :
    angularDistance z w = |(localAngle z w).val| := by
  apply angularDistance_eq_abs_of_phase z w (infinitesimalFiniteAngle (localAngle z w))
    (finitePhase_localAngle z w h)
  exact ((SignSequence.isInfinitesimal_iff_forall_real_abs_lt _).mp
    (localAngle z w).property Real.pi Real.pi_pos).le

/-- The oriented infinitesimal angle has exactly the displacement valuation. -/
theorem valuation_localAngle (z w : UnitCircle.{u})
    (h : standardPart z.val = standardPart w.val) :
    SignSequence.valuation (localAngle z w).val = valuation (w.val - z.val) := by
  have he := valuation_angularDistance z w
  rw [angularDistance_eq_abs_localAngle z w h, SignSequence.valuation_abs] at he
  rw [← neg_sub z.val w.val, valuation_neg]
  exact he

private theorem coe_relative_eq_div (z w : UnitCircle.{u}) :
    (z⁻¹ * w).val = w.val / z.val := by
  simp only [Submonoid.coe_mul, Unitary.coe_inv, div_eq_mul_inv, mul_comm]

/-- Equal-residue directions have infinitesimal relative displacement. -/
theorem infinitesimal_relative_sub_one (z w : UnitCircle.{u})
    (h : standardPart z.val = standardPart w.val) : IsInfinitesimal (w.val / z.val - 1) := by
  have hs : standardPart (z⁻¹ * w).val = 1 :=
    congrArg (fun c : Circle => (c : ℂ)) (relative_standardPart_eq_one z w h)
  have he := infinitesimal_circle_normalization (z⁻¹ * w)
  rw [hs, map_one, div_one] at he
  simpa only [coe_relative_eq_div] using he

/-- The oriented angle is literally minus `i` times the strong logarithm of the relative unit. -/
theorem ofReal_localAngle_eq_log (z w : UnitCircle.{u})
    (h : standardPart z.val = standardPart w.val) :
    ofReal (localAngle z w).val =
      -I * infLog (w.val / z.val - 1) (infinitesimal_relative_sub_one z w h) := by
  have hs : standardPart (z⁻¹ * w).val = 1 :=
    congrArg (fun c : Circle => (c : ℂ)) (relative_standardPart_eq_one z w h)
  have he := ofReal_circleSplit_snd (z⁻¹ * w)
  simp only [hs, map_one, div_one] at he
  simpa only [localAngle, coe_relative_eq_div] using he

end
end Surreal.Surcomplex
