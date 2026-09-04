import FabiusFunction.PrincipalLambertW
import FabiusFunction.LowerLambertW

/-!
# The two real branches through their gap

On `(-1/e, 0)` the two real Lambert branches are the two preimages of the
same number under `w ↦ w eʷ`, so they are not independent.  With the positive
branch gap `Δ = W₀(x) - W₋₁(x)` the Lambert W guide's "exact branch-pair
parametrization" reads

`W₀(x) = -Δ/(e^Δ - 1)`,  `W₋₁(x) = -Δ e^Δ/(e^Δ - 1)`,
`x = -Δ/(e^Δ - 1) · exp(-Δ/(e^Δ - 1))`,

or, with `t = e^Δ > 1`, `W₀ = -log t/(t - 1)` and `W₋₁ = -t log t/(t - 1)`.

## The mechanism

Dividing the two defining equations `W₀ e^{W₀} = x = W₋₁ e^{W₋₁}` gives
`W₋₁ = W₀ e^Δ`; then `Δ = W₀ - W₀ e^Δ = W₀ (1 - e^Δ)` is the whole
computation.  This module isolates the forward direction; the companion
`LambertWGapBijection` proves the guide's converse that every `Δ > 0` arises
from exactly one `x ∈ (-1/e, 0)`.
-/

set_option autoImplicit false

open Set

namespace Fabius

/-- The branch gap `Δ = W₀(x) - W₋₁(x)` is positive on `(-1/e, 0)`. -/
theorem principalLambertW_sub_lowerLambertW_pos {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    0 < principalLambertW x - lowerLambertW x := by
  have h1 := neg_one_lt_principalLambertW hx.1
  have h2 := lowerLambertW_lt_neg_one hx
  linarith

/-- **The lower branch is the principal one scaled by `e^Δ`**: on `(-1/e, 0)`,
`W₋₁(x) = W₀(x) · e^{W₀(x) - W₋₁(x)}`. -/
theorem lowerLambertW_eq_principalLambertW_mul_exp_gap {x : ℝ}
    (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    lowerLambertW x = principalLambertW x * Real.exp (principalLambertW x - lowerLambertW x) := by
  have h0 := principalLambertW_mul_exp hx.1.le
  have hm := lowerLambertW_mul_exp hx
  have he : Real.exp (lowerLambertW x) ≠ 0 := (Real.exp_pos _).ne'
  rw [Real.exp_sub]
  field_simp
  linarith

/-- **The principal branch from the gap**: `W₀(x) = -Δ/(e^Δ - 1)`. -/
theorem principalLambertW_eq_neg_gap_div {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    principalLambertW x =
      -(principalLambertW x - lowerLambertW x) /
        (Real.exp (principalLambertW x - lowerLambertW x) - 1) := by
  have hΔ := principalLambertW_sub_lowerLambertW_pos hx
  have hne : Real.exp (principalLambertW x - lowerLambertW x) - 1 ≠ 0 := by
    have : 1 < Real.exp (principalLambertW x - lowerLambertW x) := by
      rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr hΔ
    linarith
  have h := lowerLambertW_eq_principalLambertW_mul_exp_gap hx
  rw [eq_div_iff hne]
  linarith [h]

/-- **The lower branch from the gap**: `W₋₁(x) = -Δ e^Δ/(e^Δ - 1)`. -/
theorem lowerLambertW_eq_neg_gap_mul_exp_div {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    lowerLambertW x =
      -(principalLambertW x - lowerLambertW x) *
          Real.exp (principalLambertW x - lowerLambertW x) /
        (Real.exp (principalLambertW x - lowerLambertW x) - 1) := by
  have hΔ := principalLambertW_sub_lowerLambertW_pos hx
  have hne : Real.exp (principalLambertW x - lowerLambertW x) - 1 ≠ 0 := by
    have : 1 < Real.exp (principalLambertW x - lowerLambertW x) := by
      rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr hΔ
    linarith
  have h := lowerLambertW_eq_principalLambertW_mul_exp_gap hx
  -- `W₋₁ (e^Δ - 1) = -Δ e^Δ` is `W₋₁ = W₀ e^Δ` multiplied through, with
  -- `W₀ e^Δ - W₀ = -(W₀ - W₋₁)`; no rewriting of `W₋₁` inside `Δ` is needed
  rw [eq_div_iff hne]
  linear_combination (-1 : ℝ) * h

/-- **The lower branch from the gap, alternate form**:
`W₋₁(x) = -Δ/(1 - e⁻Δ)`. -/
theorem lowerLambertW_eq_neg_gap_div_one_sub_exp_neg {x : ℝ}
    (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    lowerLambertW x =
      -(principalLambertW x - lowerLambertW x) /
        (1 - Real.exp (-(principalLambertW x - lowerLambertW x))) := by
  have hΔ := principalLambertW_sub_lowerLambertW_pos hx
  have he : Real.exp (principalLambertW x - lowerLambertW x) ≠ 0 :=
    Real.exp_ne_zero _
  have hden : Real.exp (principalLambertW x - lowerLambertW x) - 1 ≠ 0 := by
    linarith [Real.one_lt_exp_iff.mpr hΔ]
  calc
    lowerLambertW x =
        -(principalLambertW x - lowerLambertW x) *
            Real.exp (principalLambertW x - lowerLambertW x) /
          (Real.exp (principalLambertW x - lowerLambertW x) - 1) :=
      lowerLambertW_eq_neg_gap_mul_exp_div hx
    _ = -(principalLambertW x - lowerLambertW x) /
          (1 - Real.exp (-(principalLambertW x - lowerLambertW x))) := by
      rw [Real.exp_neg]
      field_simp [he, hden]

/-- **The argument from the gap**: `x = W₀(x) e^{W₀(x)}` with `W₀` written
through `Δ`, i.e. `x = -Δ/(e^Δ - 1) · exp(-Δ/(e^Δ - 1))`. -/
theorem eq_neg_gap_div_mul_exp {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    x = (-(principalLambertW x - lowerLambertW x) /
          (Real.exp (principalLambertW x - lowerLambertW x) - 1)) *
        Real.exp (-(principalLambertW x - lowerLambertW x) /
          (Real.exp (principalLambertW x - lowerLambertW x) - 1)) := by
  have h := principalLambertW_mul_exp hx.1.le
  have hW := principalLambertW_eq_neg_gap_div hx
  calc x = principalLambertW x * Real.exp (principalLambertW x) := h.symm
    _ = _ := by rw [← hW]

/-- **The `t`-form**: with `t = e^Δ`, `W₀(x) = -log t/(t - 1)` and
`W₋₁(x) = -t log t/(t - 1)`. -/
theorem principalLambertW_lowerLambertW_eq_of_exp_gap {x : ℝ}
    (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    principalLambertW x =
        -Real.log (Real.exp (principalLambertW x - lowerLambertW x)) /
          (Real.exp (principalLambertW x - lowerLambertW x) - 1) ∧
      lowerLambertW x =
        -(Real.exp (principalLambertW x - lowerLambertW x) *
            Real.log (Real.exp (principalLambertW x - lowerLambertW x))) /
          (Real.exp (principalLambertW x - lowerLambertW x) - 1) := by
  rw [Real.log_exp]
  refine ⟨principalLambertW_eq_neg_gap_div hx, ?_⟩
  have h := lowerLambertW_eq_neg_gap_mul_exp_div hx
  linear_combination h

end Fabius
