import Surreal.Algebra.SmallIntegralUnits
import Surreal.Foundations.OmnificAlgebraAbsorption
import Surreal.Foundations.OmnificIntegralClosure
import Surreal.Foundations.OmnificFloor
import Surreal.Foundations.SignSequenceRealClosed
import Surreal.Foundations.SignSequenceTopology

/-!
# Small units and density of the actual omnific normalization

The actual surreal instances of `osq:nm:thm:smallunits` and
`osq:nm:thm:density`, and the proper dense inclusions in
`osq:nm:thm:normalization`. All positive surreal radii are allowed.
-/

universe u
namespace Surreal.Foundations.SignSequence
noncomputable section

/-- The exact small unit from the manuscript, as an actual surreal number. -/
def omnificSmallIntegralUnit (H : OmnificInteger.{u}) : SignSequence.{u} :=
  sqrt (omnificToSurreal H ^ 2 + 1) - omnificToSurreal H

/-- The small-unit expression is integral over the actual omnific ring. -/
theorem omnificSmallIntegralUnit_isIntegral (H : OmnificInteger.{u}) :
    IsIntegral OmnificInteger (omnificSmallIntegralUnit H) :=
  SmallIntegralUnits.sqrt_sub_isIntegral H _ (sqrt_sq (by positivity))

/-- Its inverse lies in the same integral closure. -/
theorem omnificSmallIntegralUnit_isUnit (H : OmnificInteger.{u}) :
    IsUnit (⟨omnificSmallIntegralUnit H, omnificSmallIntegralUnit_isIntegral H⟩ :
      integralClosure OmnificInteger SignSequence.{u}) :=
  SmallIntegralUnits.sqrt_sub_isUnit H _ (sqrt_sq (by positivity))

/-- The literal monic equation, inverse and sharp positive upper bound. -/
theorem omnificSmallIntegralUnit_spec (H : OmnificInteger.{u}) (hH : 0 < H) :
    omnificSmallIntegralUnit H ^ 2 +
        2 * omnificToSurreal H * omnificSmallIntegralUnit H - 1 = 0 ∧
      (omnificSmallIntegralUnit H)⁻¹ = omnificSmallIntegralUnit H + 2 * omnificToSurreal H ∧
      0 < omnificSmallIntegralUnit H ∧ omnificSmallIntegralUnit H < 1 / (2 * omnificToSurreal H) :=
  SmallIntegralUnits.sqrt_sub_spec _ _
    (by simpa only [map_zero] using omnificToSurreal_strictMono hH)
    (sqrt_nonneg _) (sqrt_sq (by positivity))

/-- The displayed family itself contains units below every positive surreal radius. -/
theorem omnific_exists_small_integral_parameter (ε : SignSequence.{u}) (hε : 0 < ε) :
    ∃ H : OmnificInteger.{u}, 0 < H ∧ omnificSmallIntegralUnit H < ε := by
  obtain ⟨H, hH, hHε⟩ := SmallIntegralUnits.exists_small_parameter
    (fun x => ⟨omnificFloor x, omnificFloor_spec x⟩) ε hε
  change 0 < omnificToSurreal H at hH
  have hH0 : 0 < H := omnificToSurreal_strictMono.lt_iff_lt.mp
    (by simpa only [map_zero] using hH)
  exact ⟨H, hH0, (omnificSmallIntegralUnit_spec H hH0).2.2.2.trans hHε⟩

/-- Actual integral units occur below every positive surreal radius. -/
theorem omnific_exists_small_integral_unit (ε : SignSequence.{u}) (hε : 0 < ε) :
    ∃ u : integralClosure OmnificInteger SignSequence.{u},
      IsUnit u ∧ 0 < (u : SignSequence) ∧ (u : SignSequence) < ε :=
  SmallIntegralUnits.exists_small_unit
    (fun x => ⟨omnificFloor x, omnificFloor_spec x⟩) ε hε

/-- The integral closure approximates every surreal from below with arbitrarily small error. -/
theorem omnific_integral_approximation (x ε : SignSequence.{u}) (hε : 0 < ε) :
    ∃ y : integralClosure OmnificInteger SignSequence.{u},
      0 ≤ x - (y : SignSequence) ∧ x - (y : SignSequence) < ε :=
  SmallIntegralUnits.exists_integral_approximation
    (fun z => ⟨omnificFloor z, omnificFloor_spec z⟩) x ε hε

/-- The actual omnific normalization is dense in the full fine order topology. -/
theorem omnific_integralClosure_dense :
    Dense (integralClosure OmnificInteger SignSequence.{u} : Set SignSequence) :=
  SmallIntegralUnits.dense_integralClosure (fun x => ⟨omnificFloor x, omnificFloor_spec x⟩)

/-- The topological closure of the normalization is the full actual surreal field. -/
theorem omnific_integralClosure_closure :
    closure (integralClosure OmnificInteger SignSequence.{u} : Set SignSequence) = Set.univ :=
  omnific_integralClosure_dense.closure_eq

/-- The original omnific subalgebra is properly contained in its integral closure. -/
theorem omnific_bot_lt_integralClosure :
    (⊥ : Subalgebra OmnificInteger SignSequence.{u}) < integralClosure OmnificInteger SignSequence := by
  refine bot_lt_iff_ne_bot.mpr ?_
  intro he
  have hx : ofReal (Real.sqrt 2) ∈ (⊥ : Subalgebra OmnificInteger SignSequence.{u}) :=
    he ▸ omnific_sqrt_two_isIntegral
  exact omnific_sqrt_two_not_mem ((Algebra.mem_bot).mp hx)

/-- The integral closure is still a proper subalgebra of the surreal field. -/
theorem omnific_integralClosure_lt_top :
    integralClosure OmnificInteger SignSequence.{u} < ⊤ := by
  rw [← omnific_completeIntegralClosure_eq_top]
  exact omnific_integralClosure_lt_completeIntegralClosure

end
end Surreal.Foundations.SignSequence
