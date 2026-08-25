import FabiusFunction.FabiusDecayComparison
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# Endpoint failure of a quotient-of-exponentials approximation

The approximation proposed in the linked Mathematica Stack Exchange question
fits the displaced compactly supported bump well on a plot.  At the left
endpoint, however, it has ordinary `exp (-c / y)` decay, which is strictly
faster than the true Fabius function.  This module formalizes that obstruction.
-/

set_option autoImplicit false

open Filter Asymptotics

namespace Fabius

/-- The exponent `3/4 * sqrt (2 pi)` from the proposed numerator. -/
noncomputable def mathematicaFabiusQuotientExponent : ℝ :=
  (3 : ℝ) / 4 * Real.sqrt (2 * Real.pi)

/-- The quotient-of-exponentials candidate proposed for the displaced bump
`x ↦ F(x+1)` on `-1 < x < 1`. -/
noncomputable def mathematicaFabiusQuotientCandidate (x : ℝ) : ℝ :=
  let ax := |x|;
  (1 + Real.exp (-(1 / ax ^ mathematicaFabiusQuotientExponent))) /
    (1 + Real.exp ((1 - 2 * ax) / (x ^ 2 - ax)))

/-- The same candidate in distance `y = x+1` from the left endpoint. -/
noncomputable def mathematicaFabiusQuotientLeft (y : ℝ) : ℝ :=
  (1 + Real.exp (-(1 /
      (1 - y) ^ mathematicaFabiusQuotientExponent))) /
    (1 + Real.exp ((1 - 2 * y) / (y * (1 - y))))

/-- On the interior of the left half, the endpoint formula is exactly the
proposed quotient evaluated at the displaced argument `x = y-1`. -/
theorem mathematicaFabiusQuotientCandidate_sub_one_eq_left
    {y : ℝ} (hy : 0 < y) (hy1 : y < 1) :
    mathematicaFabiusQuotientCandidate (y - 1) =
      mathematicaFabiusQuotientLeft y := by
  have habs : |y - 1| = 1 - y := by
    rw [abs_of_neg (sub_neg.mpr hy1)]
    ring
  have hleft : y * (1 - y) ≠ 0 :=
    mul_ne_zero hy.ne' (sub_pos.mpr hy1).ne'
  have hfull : (y - 1) ^ 2 - (1 - y) ≠ 0 := by
    rw [show (y - 1) ^ 2 - (1 - y) = -y * (1 - y) by ring]
    exact mul_ne_zero (neg_ne_zero.mpr hy.ne') (sub_pos.mpr hy1).ne'
  have hexponent :
      (1 - 2 * (1 - y)) / ((y - 1) ^ 2 - (1 - y)) =
        (1 - 2 * y) / (y * (1 - y)) := by
    rw [div_eq_div_iff hfull hleft]
    ring
  unfold mathematicaFabiusQuotientCandidate mathematicaFabiusQuotientLeft
  dsimp
  rw [habs, hexponent]

private theorem mathematicaFabiusQuotientLeft_nonneg (y : ℝ) :
    0 ≤ mathematicaFabiusQuotientLeft y := by
  unfold mathematicaFabiusQuotientLeft
  positivity

/-- On `0 < y ≤ 1 / 3`, the proposed quotient is bounded by twice an
ordinary flat exponential.  The endpoint `1 / 3` is the sharp threshold for
the exponent comparison used in this estimate. -/
theorem mathematicaFabiusQuotientLeft_le_exp_of_le_one_third {y : ℝ}
    (hy : 0 < y) (hy3 : y ≤ 1 / 3) :
    mathematicaFabiusQuotientLeft y ≤
      2 * Real.exp (-(1 / 2 : ℝ) * y⁻¹) := by
  have hy1 : y < 1 := by linarith
  have hbase : 0 < 1 - y := sub_pos.mpr hy1
  have hrpow : 0 < (1 - y) ^ mathematicaFabiusQuotientExponent :=
    Real.rpow_pos_of_pos hbase _
  have hnum :
      1 + Real.exp (-(1 /
          (1 - y) ^ mathematicaFabiusQuotientExponent)) ≤ 2 := by
    have he : Real.exp (-(1 /
        (1 - y) ^ mathematicaFabiusQuotientExponent)) ≤ 1 := by
      calc
        Real.exp (-(1 /
            (1 - y) ^ mathematicaFabiusQuotientExponent)) ≤ Real.exp 0 :=
          Real.exp_le_exp.mpr
            (neg_nonpos.mpr (one_div_nonneg.mpr hrpow.le))
        _ = 1 := Real.exp_zero
    linarith
  let A : ℝ := (1 - 2 * y) / (y * (1 - y))
  have hA : (1 / 2 : ℝ) * y⁻¹ ≤ A := by
    dsimp [A]
    rw [le_div_iff₀ (mul_pos hy hbase)]
    field_simp [hy.ne']
    nlinarith
  have hprod : 1 ≤
      Real.exp (-(1 / 2 : ℝ) * y⁻¹) * Real.exp A := by
    rw [← Real.exp_add]
    exact Real.one_le_exp (by linarith)
  unfold mathematicaFabiusQuotientLeft
  rw [div_le_iff₀ (by positivity : 0 < 1 + Real.exp A)]
  nlinarith [Real.exp_pos (-(1 / 2 : ℝ) * y⁻¹)]

/-- Compatibility specialization of
`mathematicaFabiusQuotientLeft_le_exp_of_le_one_third` to `y ≤ 1 / 4`. -/
theorem mathematicaFabiusQuotientLeft_le_exp {y : ℝ}
    (hy : 0 < y) (hy4 : y ≤ 1 / 4) :
    mathematicaFabiusQuotientLeft y ≤
      2 * Real.exp (-(1 / 2 : ℝ) * y⁻¹) :=
  mathematicaFabiusQuotientLeft_le_exp_of_le_one_third hy (by linarith)

/-- On `y = 2⁻ᵗ`, the proposed quotient is `O(exp (-(1/2) 2ᵗ))`. -/
theorem mathematicaFabiusQuotientLeft_dyadic_isBigO_exp :
    (fun t : ℝ => mathematicaFabiusQuotientLeft ((2 : ℝ) ^ (-t)))
      =O[atTop] (fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * (2 : ℝ) ^ t)) := by
  apply IsBigO.of_bound 2
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
  have hy : 0 < (2 : ℝ) ^ (-t) := Real.rpow_pos_of_pos (by norm_num) _
  have hy4 : (2 : ℝ) ^ (-t) ≤ 1 / 4 := by
    have hpow := Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ 2 by norm_num) (show -t ≤ (-2 : ℝ) by linarith)
    convert hpow using 1
    norm_num [Real.rpow_neg]
  have hinv : ((2 : ℝ) ^ (-t))⁻¹ = (2 : ℝ) ^ t := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv]
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mathematicaFabiusQuotientLeft_nonneg _),
    abs_of_pos (Real.exp_pos _)]
  simpa [hinv] using mathematicaFabiusQuotientLeft_le_exp hy hy4

/-- The quotient approximation is little-o of the true Fabius endpoint
profile along every real dyadic logarithmic scale. -/
theorem mathematicaFabiusQuotientLeft_isLittleO_fabiusLogPhi
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun t : ℝ => mathematicaFabiusQuotientLeft ((2 : ℝ) ^ (-t)))
      =o[atTop] fabiusLogPhi F :=
  mathematicaFabiusQuotientLeft_dyadic_isBigO_exp.trans_isLittleO
    (exp_neg_two_rpow_isLittleO_fabiusLogPhi F hF
      (by norm_num : (0 : ℝ) < 1 / 2))

/-- Faithful specialization to the original displaced coordinate
`x = -1 + 2⁻ᵗ`. -/
theorem mathematicaFabiusQuotientCandidate_isLittleO_fabiusLogPhi
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun t : ℝ => mathematicaFabiusQuotientCandidate ((2 : ℝ) ^ (-t) - 1))
      =o[atTop] fabiusLogPhi F := by
  apply (mathematicaFabiusQuotientLeft_isLittleO_fabiusLogPhi F hF).congr'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (mathematicaFabiusQuotientCandidate_sub_one_eq_left
      (Real.rpow_pos_of_pos (by norm_num) _)
      (Real.rpow_lt_one_of_one_lt_of_neg
        (by norm_num : (1 : ℝ) < 2) (by linarith))).symm
  · exact Filter.EventuallyEq.rfl

/-- Consequently the proposed quotient is not asymptotically equivalent to
the true displaced Fabius bump at its left endpoint. -/
theorem mathematicaFabiusQuotientCandidate_not_isEquivalent_fabiusLogPhi
    (F : BoundedFabius) (hF : IsFabius F) :
    ¬ ((fun t : ℝ =>
        mathematicaFabiusQuotientCandidate ((2 : ℝ) ^ (-t) - 1))
      ~[atTop] fabiusLogPhi F) := by
  intro hequiv
  have hlittle := mathematicaFabiusQuotientCandidate_isLittleO_fabiusLogPhi F hF
  have hself := hlittle.trans_isBigO hequiv.isBigO_symm
  have hfreq : ∃ᶠ t in (atTop : Filter ℝ),
      mathematicaFabiusQuotientCandidate ((2 : ℝ) ^ (-t) - 1) ≠ 0 :=
    (Filter.Eventually.of_forall fun t => by
      unfold mathematicaFabiusQuotientCandidate
      positivity).frequently
  exact (isLittleO_irrefl hfreq) hself

end Fabius
