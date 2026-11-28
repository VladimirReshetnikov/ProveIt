import GRHArticle.ProgressionFree.NumberFieldIdeals.IdealSmoothApproximation
import GRHArticle.ProgressionFree.NumberFieldIdeals.IdealSeparationBound
import GRHArticle.ProgressionFree.NumberFieldIdeals.SmoothNaturalLowerBound
import GRHArticle.ProgressionFree.NumberFieldIdeals.IdealUpperDensityUpper

/-!
# Finite enclosures of the ideal density suprema

The error has two independently controlled contributions. The finite
prime cutoff loses at most the field degree divided by the cutoff.
The subsequent norm cutoff loses only a computable smooth tail.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open NumberField Ideal IsDedekindDomain Finset Filter Topology
open scoped nonZeroDivisors BigOperators

variable {K : Type*} [Field K] [NumberField K]

private theorem idealSmoothLowerOptimization_le_one (integral : Bool)
    (S : Finset (HeightOneSpectrum (𝓞 K))) : idealSmoothLowerOptimization integral S ≤ 1 := by
  have hc := idealSmoothDensityFactor_pos S
  unfold idealSmoothLowerOptimization
  calc
    _ ≤ idealSmoothDensityFactor S * (idealSmoothDensityFactor S)⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ hc.le
      apply csSup_le
      · refine ⟨_, ∅, Set.empty_subset _, ?_, rfl⟩
        intro I J L hI
        exact hI.elim
      · rintro w ⟨A,hA,_,rfl⟩
        exact idealReciprocalWeight_le_smoothTotal (K := K) hA
    _ = 1 := mul_inv_cancel₀ hc.ne'

/-- Simultaneous two-sided enclosures for the actual density suprema.
Every term on the bounds has a finite rational-form expression. -/
theorem idealDensityFiniteBounds (integral : Bool) (Y H : ℕ) (hY : 0 < Y) :
    let S := primesThroughNorm K Y
    let e : ℝ := (Module.finrank ℚ K : ℝ) / Y
    let B := idealSmoothBoundedLowerOptimization integral S H
    let U := idealSmoothBoundedUpperOptimization integral S H
    B - e ≤ idealNaturalDensitySupremum K integral ∧
    idealNaturalDensitySupremum K integral ≤ B +
      idealSmoothDensityFactor S * idealReciprocalWeight (K := K) (idealSmoothNormTail S H) ∧
    U - e ≤ idealUpperDensitySupremum K integral ∧
    idealUpperDensitySupremum K integral ≤ U + idealSmoothDensityFactor S * idealSmoothFullCountTail S H := by
  dsimp only
  let S := primesThroughNorm K Y
  let v := idealSquarefreeExteriorFactor S
  let e : ℝ := (Module.finrank ℚ K : ℝ) / Y
  have hv : 0 ≤ 1-v := sub_nonneg.mpr (idealSquarefreeExteriorFactor_le_one S)
  have hvY : 1-v ≤ e := one_sub_squarefreeExteriorFactor_le_finrank_div Y hY
  have hB := idealSmoothBoundedLower_bounds integral S H
  have hU := idealSmoothBoundedUpper_bounds integral S H
  have hb := squarefree_mul_smoothLower_le_idealNaturalDensitySupremum integral S
  have hu := idealSquarefreeExteriorFactor_mul_smoothUpper_le_upperDensitySupremum integral S
  have hBe : (1-v)*idealSmoothLowerOptimization integral S ≤ e :=
    (mul_le_mul_of_nonneg_left (idealSmoothLowerOptimization_le_one integral S) hv).trans (by simpa using hvY)
  have hUe : (1-v)*idealSmoothUpperOptimization integral S ≤ e :=
    (mul_le_mul_of_nonneg_left (idealSmoothUpperOptimization_le_one integral S) hv).trans (by simpa using hvY)
  refine ⟨?_, (idealNaturalDensitySupremum_le_smoothLowerOptimization integral S).trans hB.2,
    ?_, (idealUpperDensitySupremum_le_idealSmoothUpperOptimization integral S).trans hU.2⟩
  · change idealSmoothBoundedLowerOptimization integral S H - e ≤ idealNaturalDensitySupremum K integral
    change v*idealSmoothLowerOptimization integral S ≤ idealNaturalDensitySupremum K integral at hb
    linarith only [hB.1,hb,hBe]
  · change idealSmoothBoundedUpperOptimization integral S H - e ≤ idealUpperDensitySupremum K integral
    change v*idealSmoothUpperOptimization integral S ≤ idealUpperDensitySupremum K integral at hu
    linarith only [hU.1,hu,hUe]

/-- Searching for both explicit smooth error bounds to fall below a positive
threshold succeeds for every large enough finite norm cutoff. -/
theorem eventually_idealSmoothApproximation_errors_lt (S : Finset (HeightOneSpectrum (𝓞 K)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ H : ℕ in atTop,
      idealSmoothDensityFactor S * idealReciprocalWeight (K := K) (idealSmoothNormTail S H) < ε ∧
      idealSmoothDensityFactor S * idealSmoothFullCountTail S H < ε := by
  have hL := (tendsto_idealSmoothNormTail_weight_zero S).const_mul (idealSmoothDensityFactor S)
  have hU := (tendsto_idealSmoothFullCountTail_zero S).const_mul (idealSmoothDensityFactor S)
  simp only [mul_zero] at hL hU
  exact (hL.eventually_lt_const hε).and (hU.eventually_lt_const hε)

end GRHArticle.ProgressionFree.NumberFieldIdeals
