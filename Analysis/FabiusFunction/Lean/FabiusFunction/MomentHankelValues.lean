import FabiusFunction.MomentHankelMatrix
import FabiusFunction.DyadicSpecializations

/-!
# Exact values of the up-measure's Hankel data

The orthogonal-polynomial layer's *exact certificates for the first
coefficients* begin here: the abstract moments of
`MomentHankelMatrix.lean` are identified with the corpus's exact
rational moment recursion, and the first Hankel determinants and
Jacobi ratios become explicit rationals.

* `upMoment_eq_integral_mul` — the measure moments are the density
  moments `∫ x^k·up(x) dx`;
* `upMoment_even`, `upMoment_odd`, `upMoment_zero` — the even moments
  are the exact rationals `moment n` of `Arithmetic.lean`, and the odd
  moments vanish by symmetry;
* `hankelDet_one`, `hankelDet_two` — `h_1 = 1` and
  `h_2 = moment 1 = 1/9`;
* `hankelRatio_zero`, `hankelRatio_one` — the first Jacobi ratios:
  `a_0 = 1` and `a_1 = 1/9`.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Fabius

/-- The measure moments are the density moments. -/
theorem upMoment_eq_integral_mul (F : BoundedFabius) (hF : IsFabius F)
    (k : ℕ) :
    upMoment F k = ∫ x, x ^ k * rvachevUp F x := by
  rw [upMoment, rvachevMeasure]
  have hcoe : (fun x : ℝ => ENNReal.ofReal (rvachevUp F x)) =
      fun x => ((rvachevUp F x).toNNReal : ℝ≥0∞) :=
    funext fun x => rfl
  rw [hcoe, integral_withDensity_eq_integral_smul
    ((rvachev_contDiff F hF).continuous.measurable.real_toNNReal)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [NNReal.smul_def, Real.coe_toNNReal _ (rvachevUp_nonneg F x),
    mul_comm]

/-- The even measure moments are the corpus's exact rationals. -/
theorem upMoment_even (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    upMoment F (2 * n) = (moment n : ℝ) := by
  rw [upMoment_eq_integral_mul F hF,
    integral_even_pow_mul_rvachev_eq_moment F hF]

/-- The odd measure moments vanish. -/
theorem upMoment_odd (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    upMoment F (2 * n + 1) = 0 := by
  rw [upMoment_eq_integral_mul F hF,
    integral_odd_pow_mul_rvachev_eq_zero F hF]

/-- The zeroth moment is the total mass one. -/
theorem upMoment_zero (F : BoundedFabius) (hF : IsFabius F) :
    upMoment F 0 = 1 := by
  have h := upMoment_even F hF 0
  rw [mul_zero] at h
  rw [h, moment_zero]
  norm_num

/-- The second moment is `1/9`. -/
theorem upMoment_two (F : BoundedFabius) (hF : IsFabius F) :
    upMoment F 2 = 1 / 9 := by
  have h := upMoment_even F hF 1
  rw [mul_one] at h
  rw [h, moment_one]
  norm_num

/-- The first moment vanishes. -/
theorem upMoment_one (F : BoundedFabius) (hF : IsFabius F) :
    upMoment F 1 = 0 := by
  have h := upMoment_odd F hF 0
  rwa [mul_zero, zero_add] at h

/-- `h_1 = 1`. -/
theorem hankelDet_one (F : BoundedFabius) (hF : IsFabius F) :
    hankelDet F 1 = 1 := by
  rw [hankelDet, Matrix.det_fin_one]
  show upMoment F 0 = 1
  exact upMoment_zero F hF

/-- `h_2 = moment 1 = 1/9`: the first nontrivial Hankel determinant. -/
theorem hankelDet_two (F : BoundedFabius) (hF : IsFabius F) :
    hankelDet F 2 = 1 / 9 := by
  rw [hankelDet, Matrix.det_fin_two]
  show upMoment F 0 * upMoment F 2 -
    upMoment F 1 * upMoment F 1 = 1 / 9
  rw [upMoment_zero F hF, upMoment_two F hF, upMoment_one F hF]
  ring

/-- The first Jacobi ratio: `a_0 = h_1/h_0 = 1`. -/
theorem hankelRatio_zero (F : BoundedFabius) (hF : IsFabius F) :
    hankelRatio F 0 = 1 := by
  rw [hankelRatio, hankelDet_one F hF, hankelDet_zero]
  norm_num

/-- The second Jacobi ratio: `a_1 = h_2/h_1 = 1/9` — the up-measure's
variance. -/
theorem hankelRatio_one (F : BoundedFabius) (hF : IsFabius F) :
    hankelRatio F 1 = 1 / 9 := by
  rw [hankelRatio, hankelDet_two F hF, hankelDet_one F hF]
  norm_num

end Fabius
