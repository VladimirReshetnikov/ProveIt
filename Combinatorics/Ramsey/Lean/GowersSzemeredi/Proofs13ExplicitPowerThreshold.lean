import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Combinatorics.Additive.FreimanHom
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Nat.Dist
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.ConditionalProbability
import Mathlib.RingTheory.Coprime.Lemmas

/-! Explicit thresholds for the positive-power growth conditions used in
Section 13. The definitions contain no chosen eventual-growth witnesses. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A finite threshold ensuring C <= D*x^e for positive D and e. -/
def positivePowerThreshold (C D e : Real) : Real :=
  max 1 ((max 1 (C / D)) ^ e⁻¹)

theorem positivePowerThreshold_one_le (C D e : Real) :
    1 ≤ positivePowerThreshold C D e := le_max_left _ _

/-- Equality is allowed at the threshold, with no sign restriction on C. -/
theorem positivePowerThreshold_spec {C D e x : Real} (hD : 0 < D) (he : 0 < e)
    (hx : positivePowerThreshold C D e ≤ x) : C ≤ D * x ^ e := by
  have hbase : 0 ≤ max 1 (C / D) := le_trans zero_le_one (le_max_left _ _)
  have hp : max 1 (C / D) ≤ x ^ e := by
    calc
      _ = ((max 1 (C / D)) ^ e⁻¹) ^ e := (Real.rpow_inv_rpow hbase he.ne').symm
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hbase _) ((le_max_right _ _).trans hx) he.le
  have hratio : C / D ≤ x ^ e := (le_max_right _ _).trans hp
  have h := (div_le_iff₀ hD).mp hratio
  simpa only [mul_comm] using h

end LeanProofs.GowersSzemeredi
