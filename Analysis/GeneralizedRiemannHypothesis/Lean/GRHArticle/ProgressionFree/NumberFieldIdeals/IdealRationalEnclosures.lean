import GRHArticle.ProgressionFree.NumberFieldIdeals.IdealDensityApproximation
import GRHArticle.ProgressionFree.NumberFieldIdeals.IdealOptimizationTableCorrectness

/-!
# Executable rational enclosures for the ideal density suprema

The degree term accounts for omitting primes beyond `Y`. Each interval
has width equal to that term plus one of the explicit smooth errors.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open NumberField Ideal IsDedekindDomain Finset
open scoped nonZeroDivisors

/-- Two rational intervals for the natural and upper ideal density suprema. -/
structure IdealDensityEnclosures where
  naturalLower : ℚ
  naturalUpper : ℚ
  upperLower : ℚ
  upperUpper : ℚ

/-- Finite exact computation of the two intervals from a normalized ideal table. -/
def idealRationalEnclosures {ι : Type*} [Fintype ι] [DecidableEq ι] (table : IdealCutoffTable ι)
    (primes : Multiset ℕ) (integral : Bool) (degree Y H : ℕ) : IdealDensityEnclosures where
  naturalLower := table.boundedLower primes integral H - (degree : ℚ)/Y
  naturalUpper := table.boundedLower primes integral H + table.lowerError primes H
  upperLower := table.boundedUpper primes integral H - (degree : ℚ)/Y
  upperUpper := table.boundedUpper primes integral H + table.upperError primes H

variable {K : Type*} [Field K] [NumberField K]

/-- Both rational intervals enclose their intended ideal density suprema. -/
def IdealDensityEnclosures.Sound (B : IdealDensityEnclosures) (K : Type*) [Field K] [NumberField K]
    (integral : Bool) : Prop :=
  (B.naturalLower : ℝ) ≤ idealNaturalDensitySupremum K integral ∧
  idealNaturalDensitySupremum K integral ≤ (B.naturalUpper : ℝ) ∧
  (B.upperLower : ℝ) ≤ idealUpperDensitySupremum K integral ∧
  idealUpperDensitySupremum K integral ≤ (B.upperUpper : ℝ)

/-- The rational evaluator gives valid enclosures for a certified table. -/
theorem idealRationalEnclosures_sound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T : IdealCutoffTable ι} {Y H degree : ℕ} {repr : ι → (Ideal (𝓞 K))⁰}
    (hT : T.Correct (primesThroughNorm K Y) H repr) (hY : 0 < Y)
    (hd : degree = Module.finrank ℚ K) (integral : Bool) :
    (idealRationalEnclosures T ((primesThroughNorm K Y).val.map (fun p ↦ absNorm p.asIdeal))
      integral degree Y H).Sound K integral := by
  have hBound := IdealCutoffTable.bounded_eval_eq hT integral
  have hErr := IdealCutoffTable.error_eval_eq hT
  dsimp only at hBound hErr
  simpa only [idealRationalEnclosures, IdealDensityEnclosures.Sound, Rat.cast_add, Rat.cast_sub,
    Rat.cast_div, Rat.cast_natCast, hd, hBound.1, hBound.2, hErr.1, hErr.2] using
    idealDensityFiniteBounds (K := K) integral Y H hY

/-- A successful rational tail test gives both interval widths below the
prescribed tolerance. -/
theorem idealRationalEnclosures_width_lt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : IdealCutoffTable ι) (primes : Multiset ℕ) (integral : Bool) {degree Y H : ℕ} {ε : ℚ}
    (hY : (degree : ℚ)/Y < ε/2) (hB : T.lowerError primes H < ε/2)
    (hU : T.upperError primes H < ε/2) :
    let B := idealRationalEnclosures T primes integral degree Y H
    B.naturalUpper - B.naturalLower < ε ∧ B.upperUpper - B.upperLower < ε := by
  dsimp [idealRationalEnclosures]
  constructor <;> linarith

end GRHArticle.ProgressionFree.NumberFieldIdeals
