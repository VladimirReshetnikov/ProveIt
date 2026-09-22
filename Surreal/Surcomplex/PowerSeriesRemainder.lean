import Surreal.Algebra.PowerSeriesRemainder
import Surreal.Foundations.SignSequencePowerSeries
import Surreal.Surcomplex.PowerSeries

/-!
# Exact second-order remainders at actual infinitesimals

The remainder is evaluation of the fixed formal series with coefficients
shifted by two. It is finite, its standard part is the original quadratic
coefficient, and its magnitude is bounded by that ordinary coefficient's
magnitude plus one, uniformly over every infinitesimal input. Zero inputs
are included. No convergence or growth condition on the coefficients is used.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- Evaluation of the fixed formal second-order remainder. -/
def powerSeriesSecondRemainder (x : SignSequence.{u}) (hx : IsInfinitesimal x)
    (f : PowerSeries ℝ) : SignSequence.{u} :=
  powerSeriesEvaluation x hx (FormalPowerSeries.secondOrderRemainder f)

/-- Exact constant, linear and quadratic-remainder decomposition, including at zero. -/
theorem powerSeriesEvaluation_eq_linear_add_sq_mul (x : SignSequence.{u})
    (hx : IsInfinitesimal x) (f : PowerSeries ℝ) :
    powerSeriesEvaluation x hx f = ofReal (f.coeff 0) + ofReal (f.coeff 1) * x +
      x ^ 2 * powerSeriesSecondRemainder x hx f := by
  have h := congrArg (powerSeriesEvaluation x hx)
    (FormalPowerSeries.eq_linear_add_sq_mul_secondOrderRemainder f)
  simpa only [map_add, map_mul, map_pow, powerSeriesEvaluation_C,
    powerSeriesEvaluation_X, powerSeriesSecondRemainder] using h

theorem isFinite_powerSeriesSecondRemainder (x : SignSequence.{u})
    (hx : IsInfinitesimal x) (f : PowerSeries ℝ) :
    IsFinite (powerSeriesSecondRemainder x hx f) :=
  isFinite_powerSeriesEvaluation x hx _

@[simp] theorem standardPart_powerSeriesSecondRemainder (x : SignSequence.{u})
    (hx : IsInfinitesimal x) (f : PowerSeries ℝ) :
    standardPart (powerSeriesSecondRemainder x hx f) = f.coeff 2 := by
  rw [powerSeriesSecondRemainder, standardPart_powerSeriesEvaluation,
    FormalPowerSeries.constantCoeff_secondOrderRemainder]

/-- The quadratic remainder has a single ordinary bound for all infinitesimal arguments. -/
theorem abs_powerSeriesSecondRemainder_lt (x : SignSequence.{u})
    (hx : IsInfinitesimal x) (f : PowerSeries ℝ) :
    |powerSeriesSecondRemainder x hx f| < ofReal (|f.coeff 2| + 1) := by
  have hi := infinitesimal_sub_standardPart (isFinite_powerSeriesSecondRemainder x hx f)
  rw [standardPart_powerSeriesSecondRemainder] at hi
  have hb : |powerSeriesSecondRemainder x hx f - ofReal (f.coeff 2)| < 1 := by
    simpa only [map_one] using
      (isInfinitesimal_iff_forall_real_abs_lt _).mp hi 1 (by norm_num)
  calc
    |powerSeriesSecondRemainder x hx f| =
        |(powerSeriesSecondRemainder x hx f - ofReal (f.coeff 2)) +
          ofReal (f.coeff 2)| := congrArg abs (sub_add_cancel _ _).symm
    _ ≤ |powerSeriesSecondRemainder x hx f - ofReal (f.coeff 2)| +
        |ofReal (f.coeff 2)| := abs_add_le _ _
    _ < 1 + |ofReal (f.coeff 2)| := _root_.add_lt_add_left hb _
    _ = ofReal (|f.coeff 2| + 1) := by rw [map_add, map_one, map_abs]; exact add_comm _ _

/-- A finite second-order remainder exists with the prescribed ordinary residue. -/
theorem exists_powerSeries_secondOrderRemainder (x : SignSequence.{u})
    (hx : IsInfinitesimal x) (f : PowerSeries ℝ) :
    ∃ R : SignSequence.{u}, IsFinite R ∧ standardPart R = f.coeff 2 ∧
      powerSeriesEvaluation x hx f = ofReal (f.coeff 0) + ofReal (f.coeff 1) * x + x ^ 2 * R :=
  ⟨powerSeriesSecondRemainder x hx f, isFinite_powerSeriesSecondRemainder x hx f,
    standardPart_powerSeriesSecondRemainder x hx f,
    powerSeriesEvaluation_eq_linear_add_sq_mul x hx f⟩

end
end Surreal.Foundations.SignSequence

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- Evaluation of the fixed formal second-order remainder. -/
def powerSeriesSecondRemainder (x : Surcomplex.{u}) (hx : IsInfinitesimal x)
    (f : PowerSeries ℂ) : Surcomplex.{u} :=
  powerSeriesEvaluation x hx (FormalPowerSeries.secondOrderRemainder f)

/-- Exact constant, linear and quadratic-remainder decomposition, including at zero. -/
theorem powerSeriesEvaluation_eq_linear_add_sq_mul (x : Surcomplex.{u})
    (hx : IsInfinitesimal x) (f : PowerSeries ℂ) :
    powerSeriesEvaluation x hx f = ofComplex (f.coeff 0) + ofComplex (f.coeff 1) * x +
      x ^ 2 * powerSeriesSecondRemainder x hx f := by
  have h := congrArg (powerSeriesEvaluation x hx)
    (FormalPowerSeries.eq_linear_add_sq_mul_secondOrderRemainder f)
  simpa only [map_add, map_mul, map_pow, powerSeriesEvaluation_C,
    powerSeriesEvaluation_X, powerSeriesSecondRemainder] using h

theorem isFinite_powerSeriesSecondRemainder (x : Surcomplex.{u})
    (hx : IsInfinitesimal x) (f : PowerSeries ℂ) :
    IsFinite (powerSeriesSecondRemainder x hx f) :=
  isFinite_powerSeriesEvaluation x hx _

@[simp] theorem standardPart_powerSeriesSecondRemainder (x : Surcomplex.{u})
    (hx : IsInfinitesimal x) (f : PowerSeries ℂ) :
    standardPart (powerSeriesSecondRemainder x hx f) = f.coeff 2 := by
  rw [powerSeriesSecondRemainder, standardPart_powerSeriesEvaluation,
    FormalPowerSeries.constantCoeff_secondOrderRemainder]

/-- The quadratic remainder has a single ordinary bound for all infinitesimal arguments. -/
theorem modulus_powerSeriesSecondRemainder_lt (x : Surcomplex.{u})
    (hx : IsInfinitesimal x) (f : PowerSeries ℂ) :
    modulus (powerSeriesSecondRemainder x hx f) < SignSequence.ofReal (norm (f.coeff 2) + 1) := by
  have hi := infinitesimal_sub_standardPart (isFinite_powerSeriesSecondRemainder x hx f)
  rw [standardPart_powerSeriesSecondRemainder] at hi
  have hb : modulus (powerSeriesSecondRemainder x hx f - ofComplex (f.coeff 2)) < 1 := by
    simpa only [map_one] using
      (isInfinitesimal_iff_forall_real_modulus_lt _).mp hi 1 (by norm_num)
  calc
    modulus (powerSeriesSecondRemainder x hx f) =
        modulus ((powerSeriesSecondRemainder x hx f - ofComplex (f.coeff 2)) +
          ofComplex (f.coeff 2)) := congrArg modulus (sub_add_cancel _ _).symm
    _ ≤ modulus (powerSeriesSecondRemainder x hx f - ofComplex (f.coeff 2)) +
        modulus (ofComplex (f.coeff 2)) := modulus_add_le _ _
    _ < 1 + modulus (ofComplex (f.coeff 2)) := _root_.add_lt_add_left hb _
    _ = SignSequence.ofReal (norm (f.coeff 2) + 1) := by
      rw [map_add, map_one, modulus_ofComplex]
      exact add_comm _ _

/-- A finite second-order remainder exists with the prescribed ordinary residue. -/
theorem exists_powerSeries_secondOrderRemainder (x : Surcomplex.{u})
    (hx : IsInfinitesimal x) (f : PowerSeries ℂ) :
    ∃ R : Surcomplex.{u}, IsFinite R ∧ standardPart R = f.coeff 2 ∧
      powerSeriesEvaluation x hx f = ofComplex (f.coeff 0) + ofComplex (f.coeff 1) * x + x ^ 2 * R :=
  ⟨powerSeriesSecondRemainder x hx f, isFinite_powerSeriesSecondRemainder x hx f,
    standardPart_powerSeriesSecondRemainder x hx f,
    powerSeriesEvaluation_eq_linear_add_sq_mul x hx f⟩

end
end Surreal.Surcomplex
