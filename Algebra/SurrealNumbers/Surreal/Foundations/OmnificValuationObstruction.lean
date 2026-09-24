import Surreal.Algebra.MonomialValuationObstruction
import Surreal.Foundations.SignSequenceOrderedMaps
import Surreal.Foundations.OmnificSupportBounds
import Surreal.Foundations.OmnificAlgebraAbsorption

/-!
# Small-valued valuations containing the actual omnific ring are trivial

The real clause of `osq:nm:thm:valuation`. Containment of the omnific
ring makes the valuation's exponent map monotone; smallness of its
value group forces that map to vanish. Monomial denominator clearing
then makes every field value nonnegative, and inversion gives zero.
No compatibility between the field order and the valuation is assumed.
The nonintegral half also supplies the separating failure described in
`osq:nm:rem:valsize` when only small value groups are allowed.
-/

universe u v
namespace Surreal.Foundations.SignSequence
open MonomialValuationObstruction
noncomputable section

/-- Conway monomials, packaged as a homomorphism into the native unit group. -/
def omegaPowerUnits : Multiplicative SignSequence.{u} →* SignSequence.{u}ˣ where
  toFun x := Units.mk0 (omegaPower x.toAdd) (omegaPower_ne_zero _)
  map_one' := Units.ext omegaPower_zero
  map_mul' x y := Units.ext (omegaPower_add x.toAdd y.toAdd)

@[simp] theorem omegaPowerUnits_value (x : SignSequence.{u}) :
    (omegaPowerUnits (Multiplicative.ofAdd x) : SignSequence) = omegaPower x := rfl

variable {G : Type v} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Small.{u} G]

/-- A small-valued valuation nonnegative on omnific integers vanishes on every Conway monomial. -/
theorem valuation_omegaPower_eq_zero (v : AddValuation SignSequence.{u} (WithTop G))
    (h : ∀ a : OmnificInteger.{u}, 0 ≤ v (omnificToSurreal a)) (x : SignSequence.{u}) :
    v (omegaPower x) = 0 := by
  have hw : exponentValue v omegaPowerUnits = 0 := by
    apply ordered_addHom_eq_zero
    apply exponentValue_monotone
    intro a ha
    simpa only [omegaPowerUnits_value, omnificToSurreal_monomial] using h (omnificMonomial a ha)
  have hv := coe_exponentValue v omegaPowerUnits x
  rw [hw] at hv
  exact hv.symm

/-- Monomial clearing extends nonnegativity from the omnific ring to the whole actual field. -/
theorem valuation_nonneg_of_omnific (v : AddValuation SignSequence.{u} (WithTop G))
    (h : ∀ a : OmnificInteger.{u}, 0 ≤ v (omnificToSurreal a)) (x : SignSequence.{u}) :
    0 ≤ v x := by
  obtain ⟨e, _, he⟩ := omnific_monomial_clearing (fun _ : PUnit => x)
  obtain ⟨a, _, ha⟩ := he PUnit.unit
  have hp := h a
  rwa [ha, v.map_mul, valuation_omegaPower_eq_zero v h, _root_.zero_add] at hp

/-- Every small-valued valuation whose ring contains the actual omnific integers is trivial. -/
theorem valuation_eq_zero_of_omnific (v : AddValuation SignSequence.{u} (WithTop G))
    (h : ∀ a : OmnificInteger.{u}, 0 ≤ v (omnificToSurreal a))
    (x : SignSequence.{u}) (hx : x ≠ 0) : v x = 0 :=
  eq_zero_of_nonneg v (valuation_nonneg_of_omnific v h) x hx

/-- For a small value group, containment of the actual omnific ring is equivalent to triviality. -/
theorem valuation_nonneg_omnific_iff_trivial (v : AddValuation SignSequence.{u} (WithTop G)) :
    (∀ a : OmnificInteger.{u}, 0 ≤ v (omnificToSurreal a)) ↔
      ∀ x : SignSequence.{u}, x ≠ 0 → v x = 0 := by
  refine ⟨fun h => valuation_eq_zero_of_omnific v h, ?_⟩
  intro h a
  by_cases ha : omnificToSurreal a = 0
  · simp only [ha, v.map_zero, le_top]
  · rw [h _ ha]

/-- The nonintegral half is nevertheless a unit for every small-valued valuation containing Oz. -/
theorem omnific_half_small_valuation_obstruction :
    ¬ IsIntegral OmnificInteger.{u} (2⁻¹ : SignSequence.{u}) ∧
      ∀ v : AddValuation SignSequence.{u} (WithTop G),
        (∀ a : OmnificInteger.{u}, 0 ≤ v (omnificToSurreal a)) → v 2⁻¹ = 0 := by
  refine ⟨omnific_half_almost_not_integral.2, fun v h => ?_⟩
  exact valuation_eq_zero_of_omnific v h _ (by norm_num)

end
end Surreal.Foundations.SignSequence
