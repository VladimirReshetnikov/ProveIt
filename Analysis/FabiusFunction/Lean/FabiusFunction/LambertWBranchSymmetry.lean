import FabiusFunction.LambertWGapBijection
import FabiusFunction.HyperbolicActivation

/-!
# Symmetric identities for the two real Lambert branches

On the open two-branch interval `(-exp (-1), 0)`, write

`Δ = branchGap x = W₀(x) - W₋₁(x) > 0`.

`LambertWBranchPairing` expresses each branch separately through `Δ`, while
`LambertWGapBijection` proves that `Δ` is a global coordinate on this
interval.  This file packages the symmetric consequences:

* `W₋₁ / W₀ = exp Δ`;
* `W₀ + W₋₁ = -Δ cosh (Δ / 2) / sinh (Δ / 2)`;
* `W₀ W₋₁ = Δ² / (4 sinh (Δ / 2)²)`;
* the strict bounds `W₀ + W₋₁ < -2` and `0 < W₀ W₋₁ < 1`.

All statements deliberately exclude the branch point `Δ = 0` and the
singular endpoint `x = 0`.
-/

set_option autoImplicit false

open Set

namespace Fabius

noncomputable section

/-! ## Exact symmetric identities -/

/-- The quotient of the lower branch by the principal branch is the
exponential of their positive gap. -/
theorem lowerLambertW_div_principalLambertW_eq_exp_branchGap {x : ℝ}
    (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    lowerLambertW x / principalLambertW x = Real.exp (branchGap x) := by
  have hW0 : principalLambertW x ≠ 0 := by
    intro h
    have heq := principalLambertW_mul_exp hx.1.le
    rw [h, zero_mul] at heq
    exact hx.2.ne heq.symm
  apply (div_eq_iff hW0).2
  rw [branchGap, mul_comm]
  exact lowerLambertW_eq_principalLambertW_mul_exp_gap hx

/-- Exponential-rational form of the sum of the two real branches. -/
theorem principalLambertW_add_lowerLambertW_eq_exp_branchGap {x : ℝ}
    (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    principalLambertW x + lowerLambertW x =
      -branchGap x * (Real.exp (branchGap x) + 1) /
        (Real.exp (branchGap x) - 1) := by
  have h₀ : principalLambertW x =
      -branchGap x / (Real.exp (branchGap x) - 1) := by
    simpa only [branchGap] using principalLambertW_eq_neg_gap_div hx
  have hm : lowerLambertW x =
      -branchGap x * Real.exp (branchGap x) /
        (Real.exp (branchGap x) - 1) := by
    simpa only [branchGap] using lowerLambertW_eq_neg_gap_mul_exp_div hx
  calc
    principalLambertW x + lowerLambertW x =
        -branchGap x / (Real.exp (branchGap x) - 1) +
          (-branchGap x * Real.exp (branchGap x) /
            (Real.exp (branchGap x) - 1)) := congrArg₂ (· + ·) h₀ hm
    _ = _ := by ring

/-- Hyperbolic form of the sum:
`W₀ + W₋₁ = -Δ cosh(Δ/2) / sinh(Δ/2)`. -/
theorem principalLambertW_add_lowerLambertW_eq_cosh_div_sinh_branchGap
    {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    principalLambertW x + lowerLambertW x =
      -branchGap x * Real.cosh (branchGap x / 2) /
        Real.sinh (branchGap x / 2) := by
  rw [principalLambertW_add_lowerLambertW_eq_exp_branchGap hx]
  have hd : 0 < branchGap x := by
    simpa only [branchGap] using principalLambertW_sub_lowerLambertW_pos hx
  have hehalf : Real.exp (branchGap x) =
      Real.exp (branchGap x / 2) * Real.exp (branchGap x / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [Real.cosh_eq, Real.sinh_eq, Real.exp_neg, hehalf]
  field_simp [Real.exp_ne_zero, hd.ne']

/-- Exponential-rational form of the product of the two real branches. -/
theorem principalLambertW_mul_lowerLambertW_eq_exp_branchGap {x : ℝ}
    (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    principalLambertW x * lowerLambertW x =
      branchGap x ^ 2 * Real.exp (branchGap x) /
        (Real.exp (branchGap x) - 1) ^ 2 := by
  have hd : 0 < branchGap x := by
    simpa only [branchGap] using principalLambertW_sub_lowerLambertW_pos hx
  have hden : Real.exp (branchGap x) - 1 ≠ 0 := by
    linarith [Real.one_lt_exp_iff.mpr hd]
  have h₀ : principalLambertW x =
      -branchGap x / (Real.exp (branchGap x) - 1) := by
    simpa only [branchGap] using principalLambertW_eq_neg_gap_div hx
  have hm : lowerLambertW x =
      -branchGap x * Real.exp (branchGap x) /
        (Real.exp (branchGap x) - 1) := by
    simpa only [branchGap] using lowerLambertW_eq_neg_gap_mul_exp_div hx
  calc
    principalLambertW x * lowerLambertW x =
        (-branchGap x / (Real.exp (branchGap x) - 1)) *
          (-branchGap x * Real.exp (branchGap x) /
            (Real.exp (branchGap x) - 1)) := congrArg₂ (· * ·) h₀ hm
    _ = _ := by
      field_simp [hden]

/-- Hyperbolic form of the product:
`W₀ W₋₁ = Δ² / (4 sinh(Δ/2)²)`. -/
theorem principalLambertW_mul_lowerLambertW_eq_sinh_sq_branchGap {x : ℝ}
    (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    principalLambertW x * lowerLambertW x =
      branchGap x ^ 2 / (4 * Real.sinh (branchGap x / 2) ^ 2) := by
  rw [principalLambertW_mul_lowerLambertW_eq_exp_branchGap hx]
  have hd : 0 < branchGap x := by
    simpa only [branchGap] using principalLambertW_sub_lowerLambertW_pos hx
  have hehalf : Real.exp (branchGap x) =
      Real.exp (branchGap x / 2) * Real.exp (branchGap x / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [Real.sinh_eq, Real.exp_neg, hehalf]
  field_simp [Real.exp_ne_zero, hd.ne']
  ring

/-! ## Strict interior bounds -/

/-- The sum of the two real branches is strictly less than `-2` in the
interior of their common domain. -/
theorem principalLambertW_add_lowerLambertW_lt_neg_two {x : ℝ}
    (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    principalLambertW x + lowerLambertW x < -2 := by
  rw [principalLambertW_add_lowerLambertW_eq_cosh_div_sinh_branchGap hx]
  have hd : 0 < branchGap x := by
    simpa only [branchGap] using principalLambertW_sub_lowerLambertW_pos hx
  have hy : 0 < branchGap x / 2 := half_pos hd
  have hs : 0 < Real.sinh (branchGap x / 2) := Real.sinh_pos_iff.mpr hy
  rw [div_lt_iff₀ hs]
  have hsc := sinh_lt_mul_cosh hy
  nlinarith

/-- The product of the two negative real branches is positive. -/
theorem principalLambertW_mul_lowerLambertW_pos {x : ℝ}
    (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    0 < principalLambertW x * lowerLambertW x := by
  have hd : 0 < branchGap x := by
    simpa only [branchGap] using principalLambertW_sub_lowerLambertW_pos hx
  have hformula : principalLambertW x =
      -branchGap x / (Real.exp (branchGap x) - 1) := by
    simpa only [branchGap] using principalLambertW_eq_neg_gap_div hx
  have hW0 : principalLambertW x < 0 := by
    rw [hformula]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hd)
      (sub_pos.mpr (Real.one_lt_exp_iff.mpr hd))
  exact mul_pos_of_neg_of_neg hW0
    (lowerLambertW_lt_neg_one hx |>.trans (by norm_num))

/-- The product of the two real branches is strictly less than one. -/
theorem principalLambertW_mul_lowerLambertW_lt_one {x : ℝ}
    (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    principalLambertW x * lowerLambertW x < 1 := by
  rw [principalLambertW_mul_lowerLambertW_eq_sinh_sq_branchGap hx]
  have hd : 0 < branchGap x := by
    simpa only [branchGap] using principalLambertW_sub_lowerLambertW_pos hx
  have hy : 0 < branchGap x / 2 := half_pos hd
  have hs : 0 < Real.sinh (branchGap x / 2) := Real.sinh_pos_iff.mpr hy
  have hys := Real.self_lt_sinh_iff.mpr hy
  have hsq : (branchGap x / 2) ^ 2 < Real.sinh (branchGap x / 2) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hys) (add_pos hs hy)]
  rw [div_lt_one (by positivity : 0 < 4 * Real.sinh (branchGap x / 2) ^ 2)]
  nlinarith

/-- The product of the two real branches belongs to the open unit interval. -/
theorem principalLambertW_mul_lowerLambertW_mem_Ioo {x : ℝ}
    (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    principalLambertW x * lowerLambertW x ∈ Ioo 0 1 :=
  ⟨principalLambertW_mul_lowerLambertW_pos hx,
    principalLambertW_mul_lowerLambertW_lt_one hx⟩

end

end Fabius
