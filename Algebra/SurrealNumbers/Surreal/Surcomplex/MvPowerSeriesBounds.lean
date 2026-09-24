import Surreal.Surcomplex.PowerSeriesRemainder
import Surreal.Surcomplex.MvPowerSeries
import Surreal.Foundations.SignSequenceMvPowerSeries

/-!
# Uniform ordinary bounds for infinitesimal formal substitution

Every finite scalar differs infinitesimally from its ordinary standard part.
Its magnitude is therefore less than the ordinary standard-part magnitude
plus one. For finite-variable formal evaluation this supplies one bound,
determined only by the constant coefficient, for every infinitesimal input.
This is the uniform remainder estimate needed for fine Taylor differentiation.
It supplies the uniform bound in the proof of `trigonometry:prop:lift`.
-/

universe u v

namespace Surreal.Foundations.SignSequence

/-- A finite surreal is bounded using its exact ordinary residue. -/
theorem abs_lt_standardPart_add_one (x : SignSequence.{u}) (hx : IsFinite x) :
    |x| < ofReal (|standardPart x| + 1) := by
  have hsmall := infinitesimal_sub_standardPart hx
  have hb : |x - ofReal (standardPart x)| < 1 := by
    simpa only [map_one] using
      (isInfinitesimal_iff_forall_real_abs_lt _).mp hsmall 1 (by norm_num)
  calc
    |x| = |(x - ofReal (standardPart x)) + ofReal (standardPart x)| := by
      rw [sub_add_cancel]
    _ ≤ |x - ofReal (standardPart x)| + |ofReal (standardPart x)| := abs_add_le _ _
    _ < 1 + |ofReal (standardPart x)| := _root_.add_lt_add_left hb _
    _ = ofReal (|standardPart x| + 1) := by
      rw [map_add, map_abs, map_one]
      exact add_comm _ _

/-- A single ordinary bound works for every infinitesimal tuple, with no coefficient-growth bound. -/
theorem abs_mvPowerSeriesEvaluation_lt {σ : Type v} [Fintype σ]
    (x : σ → SignSequence.{u}) (hx : ∀ i, IsInfinitesimal (x i))
    (F : MvPowerSeries σ ℝ) :
    |mvPowerSeriesEvaluation x hx F| < ofReal (|MvPowerSeries.constantCoeff F| + 1) := by
  simpa only [standardPart_mvPowerSeriesEvaluation] using
    abs_lt_standardPart_add_one (mvPowerSeriesEvaluation x hx F)
      (isFinite_mvPowerSeriesEvaluation x hx F)

end Surreal.Foundations.SignSequence

namespace Surreal.Surcomplex

open Foundations

/-- A finite surcomplex is bounded using the ordinary norm of its exact residue. -/
theorem modulus_lt_standardPart_add_one (z : Surcomplex.{u}) (hz : IsFinite z) :
    modulus z < SignSequence.ofReal (norm (standardPart z) + 1) := by
  have hsmall := infinitesimal_sub_standardPart hz
  have hb : modulus (z - ofComplex (standardPart z)) < 1 := by
    simpa only [map_one] using
      (isInfinitesimal_iff_forall_real_modulus_lt _).mp hsmall 1 (by norm_num)
  calc
    modulus z = modulus ((z - ofComplex (standardPart z)) + ofComplex (standardPart z)) := by
      rw [sub_add_cancel]
    _ ≤ modulus (z - ofComplex (standardPart z)) + modulus (ofComplex (standardPart z)) :=
      modulus_add_le _ _
    _ < 1 + modulus (ofComplex (standardPart z)) := _root_.add_lt_add_left hb _
    _ = SignSequence.ofReal (norm (standardPart z) + 1) := by
      rw [map_add, modulus_ofComplex, map_one]
      exact add_comm _ _

/-- The bound depends only on the formal constant coefficient, uniformly over infinitesimal tuples. -/
theorem modulus_mvPowerSeriesEvaluation_lt {σ : Type v} [Fintype σ]
    (x : σ → Surcomplex.{u}) (hx : ∀ i, IsInfinitesimal (x i))
    (F : MvPowerSeries σ ℂ) :
    modulus (mvPowerSeriesEvaluation x hx F) <
      SignSequence.ofReal (norm (MvPowerSeries.constantCoeff F) + 1) := by
  simpa only [standardPart_mvPowerSeriesEvaluation] using
    modulus_lt_standardPart_add_one (mvPowerSeriesEvaluation x hx F)
      (isFinite_mvPowerSeriesEvaluation x hx F)

end Surreal.Surcomplex
