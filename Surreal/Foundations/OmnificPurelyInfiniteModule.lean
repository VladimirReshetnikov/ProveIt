import Surreal.Foundations.OmnificIntegers
import Mathlib.Algebra.Module.TransferInstance

/-!
# The rational vector space of purely infinite omnific integers

The vector-space prerequisite for `odg:thm:linear`. Transport the established
real support submodule to the actual omnific ideal, preserving its existing
additive group, and restrict scalars to the ordinary rationals.
-/

universe u
namespace Surreal.Foundations.SignSequence

noncomputable section

/-- The actual omnific purely infinite ideal is additively the existing real support submodule. -/
def omnificPurelyInfiniteAddEquiv : omnificPurelyInfiniteIdeal.{u} ≃+ purelyInfiniteSubmodule.{u} where
  toFun x := ⟨x.val.val, (mem_purelyInfiniteSubmodule_iff _).mpr
    ((mem_omnificPurelyInfiniteIdeal_iff _).mp x.property)⟩
  invFun x := ⟨⟨x.val, purelyInfinite_mem_omnificSubring x.val x.property⟩,
    (mem_omnificPurelyInfiniteIdeal_iff _).mpr ((mem_purelyInfiniteSubmodule_iff _).mp x.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Real coefficients act on the actual purely infinite omnific ideal. -/
instance omnificPurelyInfiniteRealModule : Module ℝ omnificPurelyInfiniteIdeal.{u} :=
  omnificPurelyInfiniteAddEquiv.module ℝ

/-- Ordinary rational coefficients act on the actual purely infinite omnific ideal. -/
instance omnificPurelyInfiniteRatModule : Module ℚ omnificPurelyInfiniteIdeal.{u} :=
  Module.compHom _ (algebraMap ℚ ℝ)

/-- The transported real action is literal real multiplication in the surreal field. -/
theorem omnificPurelyInfinite_real_smul (r : ℝ) (x : omnificPurelyInfiniteIdeal.{u}) :
    omnificToSurreal (r • x).val = ofReal r * omnificToSurreal x.val := rfl

/-- The rational action is multiplication by the canonical rational surreal. -/
theorem omnificPurelyInfinite_rat_smul (r : ℚ) (x : omnificPurelyInfiniteIdeal.{u}) :
    omnificToSurreal (r • x).val = (r : SignSequence.{u}) * omnificToSurreal x.val := by
  change ofReal (r : ℝ) * omnificToSurreal x.val = _
  rw [map_ratCast]

/-- Rational scalar multiplication by an integer agrees with multiplication in the omnific ring. -/
theorem omnificPurelyInfinite_int_smul (r : ℤ) (x : omnificPurelyInfiniteIdeal.{u}) :
    (((r : ℚ) • x).val) = omnificIntCast r * x.val := by
  apply omnificToSurreal_injective
  rw [omnificPurelyInfinite_rat_smul, map_mul, omnificToSurreal_intCast, Rat.cast_intCast]

end
end Surreal.Foundations.SignSequence
