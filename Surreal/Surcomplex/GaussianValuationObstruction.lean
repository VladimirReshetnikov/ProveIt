import Surreal.Foundations.OmnificValuationObstruction
import Surreal.Surcomplex.GaussianNormalizationEmbedding
import Surreal.Surcomplex.GaussianAlgebraAbsorption

/-!
# Small-valued valuations containing Gaussian omnific integers are trivial

The Gaussian clause of `osq:nm:thm:valuation`. Restrict to the actual
real field to kill every real Conway monomial. The existing Gaussian
monomial clearing theorem then forces every value to be nonnegative.
The half witness records the nonintegrality obstruction from
`osq:nm:rem:valsize` for the Gaussian ring too.
-/

universe u v
namespace Surreal.Surcomplex
open Foundations MonomialValuationObstruction
noncomputable section

variable {G : Type v} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Small.{u} G]

/-- Nonnegative Gaussian omnific values force zero value on every real Conway monomial. -/
theorem valuation_real_omegaPower_eq_zero (v : AddValuation Surcomplex.{u} (WithTop G))
    (h : ∀ a : GaussianOmnificInteger.{u}, 0 ≤ v (gaussianOmnificToSurcomplex a))
    (x : SignSequence.{u}) : v (ofReal (SignSequence.omegaPower x)) = 0 := by
  apply SignSequence.valuation_omegaPower_eq_zero (v.comap ofReal)
  intro a
  exact h (omnificToGaussian a)

/-- Gaussian monomial clearing extends nonnegativity to every actual surcomplex number. -/
theorem valuation_nonneg_of_gaussianOmnific (v : AddValuation Surcomplex.{u} (WithTop G))
    (h : ∀ a : GaussianOmnificInteger.{u}, 0 ≤ v (gaussianOmnificToSurcomplex a))
    (x : Surcomplex.{u}) : 0 ≤ v x := by
  obtain ⟨e, _, he⟩ := gaussianOmnific_monomial_clearing (fun _ : PUnit => x)
  obtain ⟨a, _, ha⟩ := he PUnit.unit
  have hp := h a
  rwa [ha, v.map_mul, valuation_real_omegaPower_eq_zero v h, _root_.zero_add] at hp

/-- Every small-valued valuation containing the actual Gaussian omnific ring is trivial. -/
theorem valuation_eq_zero_of_gaussianOmnific (v : AddValuation Surcomplex.{u} (WithTop G))
    (h : ∀ a : GaussianOmnificInteger.{u}, 0 ≤ v (gaussianOmnificToSurcomplex a))
    (x : Surcomplex.{u}) (hx : x ≠ 0) : v x = 0 :=
  eq_zero_of_nonneg v (valuation_nonneg_of_gaussianOmnific v h) x hx

/-- Containment of the Gaussian omnific ring characterizes small-valued trivial valuations. -/
theorem valuation_nonneg_gaussianOmnific_iff_trivial (v : AddValuation Surcomplex.{u} (WithTop G)) :
    (∀ a : GaussianOmnificInteger.{u}, 0 ≤ v (gaussianOmnificToSurcomplex a)) ↔
      ∀ x : Surcomplex.{u}, x ≠ 0 → v x = 0 := by
  refine ⟨fun h => valuation_eq_zero_of_gaussianOmnific v h, ?_⟩
  intro h a
  by_cases ha : gaussianOmnificToSurcomplex a = 0
  · simp only [ha, v.map_zero, le_top]
  · rw [h _ ha]

/-- The Gaussian nonintegral half also has value zero under every small-valued containing valuation. -/
theorem gaussianOmnific_half_small_valuation_obstruction :
    ¬ IsIntegral GaussianOmnificInteger.{u} (2⁻¹ : Surcomplex.{u}) ∧
      ∀ v : AddValuation Surcomplex.{u} (WithTop G),
        (∀ a : GaussianOmnificInteger.{u}, 0 ≤ v (gaussianOmnificToSurcomplex a)) → v 2⁻¹ = 0 := by
  refine ⟨gaussianOmnific_half_almost_not_integral.2, fun v h => ?_⟩
  exact valuation_eq_zero_of_gaussianOmnific v h _ (by norm_num)

end
end Surreal.Surcomplex
