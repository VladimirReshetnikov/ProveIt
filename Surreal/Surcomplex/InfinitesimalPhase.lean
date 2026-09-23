import Surreal.Algebra.ComplexEulerSeries
import Surreal.Surcomplex.InfinitesimalTrigonometry
import Surreal.Surcomplex.FiniteExponential
import Surreal.Surcomplex.PowerSeriesDerivative
import Surreal.Algebra.FineDerivativeRules

/-!
# The exponential angular coordinate on the infinitesimal monad

Euler's identity connects the actual exponential and trigonometric Taylor
germs. Its addition law provides exact local cosine expansions. The
coordinate has nonzero fine derivative, as required by the angular
multiplicity convention in `trigonometry:thm:polyroots` and its cosine-fold
instance `trigonometry:thm:fold`.
-/

universe u
namespace Surreal.Surcomplex

open Foundations
noncomputable section

/-- Multiplication by the ordinary imaginary unit preserves infinitesimality. -/
theorem infinitesimal_I_mul {z : Surcomplex.{u}} (hz : IsInfinitesimal z) :
    IsInfinitesimal (I * z) := by
  simpa only [ofComplex_I] using infinitesimal_ofComplex_mul Complex.I hz

/-- The exponential angular coordinate at an actual infinitesimal angle. -/
def infinitesimalPhase (z : Surcomplex.{u}) (hz : IsInfinitesimal z) : Surcomplex.{u} :=
  infExp (I * z) (infinitesimal_I_mul hz)

/-- This coordinate agrees with the established finite exponential at the same argument. -/
theorem infinitesimalPhase_eq_finiteExp (z : Surcomplex.{u}) (hz : IsInfinitesimal z) :
    infinitesimalPhase z hz = finiteExp
      ⟨I * z, finite_of_infinitesimal (infinitesimal_I_mul hz)⟩ :=
  (finiteExp_of_isInfinitesimal _ _).symm

/-- Exact Euler identity in the actual surcomplex field. -/
theorem infinitesimalPhase_eq (z : Surcomplex.{u}) (hz : IsInfinitesimal z) :
    infinitesimalPhase z hz = infCos z hz + I * infSin z hz := by
  have h := congrArg (powerSeriesEvaluation z hz) Analytic.complexEulerSeries
  rw [powerSeriesEvaluation_subst_const_mul_X z hz Complex.I _
    (by simpa only [ofComplex_I] using infinitesimal_I_mul hz)] at h
  simpa only [infinitesimalPhase, infExp, infCos, infSin, map_add, map_mul,
    powerSeriesEvaluation_C, ofComplex_I] using h

theorem infinitesimalPhase_ne_zero (z : Surcomplex.{u}) (hz : IsInfinitesimal z) :
    infinitesimalPhase z hz ≠ 0 := infExp_ne_zero _ _

@[simp] theorem infinitesimalPhase_zero :
    infinitesimalPhase (0 : Surcomplex.{u}) infinitesimal_zero = 1 := by
  rw [infinitesimalPhase_eq, infCos_zero, infSin_zero, mul_zero, add_zero]

/-- Adding infinitesimal angles multiplies their exponential coordinates. -/
theorem infinitesimalPhase_add (z w : Surcomplex.{u})
    (hz : IsInfinitesimal z) (hw : IsInfinitesimal w) :
    infinitesimalPhase (z + w) (infinitesimal_add hz hw) =
      infinitesimalPhase z hz * infinitesimalPhase w hw := by
  have h := infExp_add (I * z) (I * w) (infinitesimal_I_mul hz) (infinitesimal_I_mul hw)
  have he : I * (z + w) = I * z + I * w := mul_add _ _ _
  exact (show infinitesimalPhase (z + w) _ = infExp (I * z + I * w) _ by
    unfold infinitesimalPhase
    congr 1).trans h

/-- Negation of an angle inverts its nonzero coordinate. -/
theorem infinitesimalPhase_neg (z : Surcomplex.{u}) (hz : IsInfinitesimal z) :
    infinitesimalPhase (-z) (infinitesimal_neg hz) = (infinitesimalPhase z hz)⁻¹ := by
  have h := infExp_neg (I * z) (infinitesimal_I_mul hz)
  exact (show infinitesimalPhase (-z) _ = infExp (-(I * z)) _ by
    unfold infinitesimalPhase
    congr 1
    ring).trans h

/-- The reciprocal Euler identity uses the same sine and cosine germs. -/
theorem infinitesimalPhase_inv (z : Surcomplex.{u}) (hz : IsInfinitesimal z) :
    (infinitesimalPhase z hz)⁻¹ = infCos z hz - I * infSin z hz := by
  rw [← infinitesimalPhase_neg, infinitesimalPhase_eq, infCos_neg, infSin_neg,
    mul_neg, sub_eq_add_neg]

/-- Cosine is the Laurent polynomial `(u+u⁻¹)/2` in the actual exponential coordinate. -/
theorem infCos_eq_phase (z : Surcomplex.{u}) (hz : IsInfinitesimal z) :
    infCos z hz = (infinitesimalPhase z hz + (infinitesimalPhase z hz)⁻¹) / 2 := by
  rw [infinitesimalPhase_inv, infinitesimalPhase_eq]
  ring

/-- The complex addition formula holds throughout the actual infinitesimal monad. -/
theorem infCos_add (z w : Surcomplex.{u}) (hz : IsInfinitesimal z) (hw : IsInfinitesimal w) :
    infCos (z + w) (infinitesimal_add hz hw) =
      infCos z hz * infCos w hw - infSin z hz * infSin w hw := by
  rw [infCos_eq_phase, infinitesimalPhase_add z w hz hw, mul_inv_rev,
    infinitesimalPhase_inv, infinitesimalPhase_inv, infinitesimalPhase_eq, infinitesimalPhase_eq]
  linear_combination infSin z hz * infSin w hw * I_sq

/-- A total representative of the exponential angular germ. -/
def infinitesimalPhaseFunction (z : Surcomplex.{u}) : Surcomplex.{u} :=
  powerSeriesFunction (PowerSeries.exp ℂ) (I * z)

theorem infinitesimalPhaseFunction_eq (z : Surcomplex.{u}) (hz : IsInfinitesimal z) :
    infinitesimalPhaseFunction z = infinitesimalPhase z hz :=
  powerSeriesFunction_of_isInfinitesimal _ _ (infinitesimal_I_mul hz)

/-- The fine derivative of the angular coordinate is the nonzero scalar `iu`. -/
theorem fineHasDerivAt_infinitesimalPhase (z : Surcomplex.{u}) (hz : IsInfinitesimal z) :
    FineHasDerivAt infinitesimalPhaseFunction (infinitesimalPhase z hz * I) z := by
  have he := fineHasDerivAt_powerSeriesFunction (PowerSeries.exp ℂ) (I * z) (infinitesimal_I_mul hz)
  rw [PowerSeries.derivative_exp] at he
  have hi : FineHasDerivAt (fun w : Surcomplex.{u} => I * w) I z := by
    simpa only [zero_mul, mul_one, zero_add] using
      (FineHasDerivAt.const I z).mul (FineHasDerivAt.id z)
  exact he.comp hi

theorem infinitesimalPhase_derivative_ne_zero (z : Surcomplex.{u}) (hz : IsInfinitesimal z) :
    infinitesimalPhase z hz * I ≠ 0 :=
  mul_ne_zero (infinitesimalPhase_ne_zero z hz) (by
    intro h
    have he : (I : Surcomplex.{u}) ^ 2 = -1 := I_sq
    rw [h] at he
    norm_num at he)

end
end Surreal.Surcomplex
