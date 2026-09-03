import FabiusFunction.LowerLambertW

/-!
# Near-zero logarithmic bounds for the lower Lambert branch

For `-1/e < x < 0` put `η = log (1 / (-x)) > 1`.  Then

`-η - η·log η / (η - 1) ≤ W₋₁(x) < -η - log η`.

This is the "near-zero logarithmic bounds" theorem of the Lambert W guide.

## The mechanism, and why it is stated for `z - log z` first

Write `y = -W₋₁(x) > 1`.  The defining equation `W e^W = x` becomes
`y·e^{-y} = -x`, i.e. `y - log y = η`.  So the theorem is a statement about
the *inverse* of the map `φ(z) = z - log z`, which is strictly increasing on
`(1, ∞)`: whenever `φ(y) = η`,

* `y > η + log η`, because `y > η` forces `log y > log η`; and
* `y ≤ B := η + η·log η / (η - 1)`, because `log B ≤ log η + (B - η)/η`
  shows `φ(B) ≥ η = φ(y)`, and `φ` is monotone.

Neither step mentions Lambert's function, so the bracket is proved for an
arbitrary `y > 1` and `η = φ(y)` in `Fabius.SubLog`, and then read off for
`W₋₁` through `lowerLambertW_mul_exp`.  Stated this way it applies to any
quantity known only through an equation `y - log y = η` — which is how the
lower branch enters the dyadic saddle-point analysis elsewhere in this
library.
-/

set_option autoImplicit false

open Set

namespace Fabius

/-! ### The map `z ↦ z - log z` on `(1, ∞)` -/

namespace SubLog

/-- `z ↦ z - log z` is strictly increasing on `[1, ∞)`: its derivative
`1 - 1/z` is positive for `z > 1`. -/
theorem strictMonoOn_sub_log : StrictMonoOn (fun z : ℝ => z - Real.log z) (Ici 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 1) ?_ ?_
  · exact (continuousOn_id.sub (Real.continuousOn_log.mono fun z hz =>
      by simp only [mem_Ici, mem_compl_iff, mem_singleton_iff] at hz ⊢; linarith))
  · intro z hz
    rw [interior_Ici, mem_Ioi] at hz
    have hz0 : z ≠ 0 := by linarith
    have hd : HasDerivAt (fun z : ℝ => z - Real.log z) (1 - z⁻¹) z :=
      (hasDerivAt_id z).sub (Real.hasDerivAt_log hz0)
    rw [hd.deriv]
    have : z⁻¹ < 1 := inv_lt_one_of_one_lt₀ hz
    linarith

/-- A point `y > 1` with `y - log y = η` lies strictly above `η + log η`. -/
theorem lt_of_sub_log_eq {y η : ℝ} (hy : 1 < y) (h : y - Real.log y = η) :
    η + Real.log η < y := by
  have hlog : 0 < Real.log y := Real.log_pos hy
  have hη : η < y := by linarith
  have hη1 : 1 < η := by
    -- `η = y - log y` and `log y < y - 1`
    have := Real.log_lt_sub_one_of_pos (by linarith : 0 < y) hy.ne'
    linarith
  have := Real.log_lt_log (by linarith) hη
  linarith

/-- A point `y > 1` with `y - log y = η` lies at most at
`η + η·log η / (η - 1)`. -/
theorem le_of_sub_log_eq {y η : ℝ} (hy : 1 < y) (h : y - Real.log y = η) :
    y ≤ η + η * Real.log η / (η - 1) := by
  have hη1 : 1 < η := by
    have := Real.log_lt_sub_one_of_pos (by linarith : 0 < y) hy.ne'
    linarith
  have hη0 : 0 < η := by linarith
  have hlogη : 0 < Real.log η := Real.log_pos hη1
  set r := η * Real.log η / (η - 1) with hr
  have hr0 : 0 < r := by positivity
  -- `log (η + r) ≤ log η + r/η`, from `log (1 + s) ≤ s` at `s = r/η`
  have hlogB : Real.log (η + r) ≤ Real.log η + r / η := by
    have hs : 0 < 1 + r / η := by positivity
    have h1 : Real.log (η + r) = Real.log η + Real.log (1 + r / η) := by
      rw [← Real.log_mul hη0.ne' hs.ne']
      congr 1
      field_simp
    have h2 : Real.log (1 + r / η) ≤ r / η := by
      linarith [Real.log_le_sub_one_of_pos hs]
    linarith
  -- and `r/η = log η / (η - 1)`, so `log η + r/η = r`
  have hrη : Real.log η + r / η = r := by
    have hne : η - 1 ≠ 0 := by linarith
    rw [hr]
    field_simp
    ring
  -- hence `φ(η + r) ≥ η = φ(y)`, and `φ` is increasing on `[1, ∞)`
  have hφB : η ≤ (η + r) - Real.log (η + r) := by linarith
  refine le_of_not_gt fun hcon => ?_
  have hmono := strictMonoOn_sub_log (mem_Ici.mpr (by linarith : (1 : ℝ) ≤ η + r))
    (mem_Ici.mpr hy.le) hcon
  simp only at hmono
  linarith

/-- **The bracket for the inverse of `z - log z`.**  If `y > 1` and
`y - log y = η`, then `η + log η < y ≤ η + η·log η / (η - 1)`. -/
theorem bracket_of_sub_log_eq {y η : ℝ} (hy : 1 < y) (h : y - Real.log y = η) :
    η + Real.log η < y ∧ y ≤ η + η * Real.log η / (η - 1) :=
  ⟨lt_of_sub_log_eq hy h, le_of_sub_log_eq hy h⟩

end SubLog

/-! ### The lower branch near zero -/

/-- On `(-1/e, 0)`, the lower branch satisfies `y - log y = log (1 / (-x))`
with `y = -W₋₁(x)`: the defining equation read through `y·e^{-y} = -x`. -/
theorem neg_lowerLambertW_sub_log_eq {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    -lowerLambertW x - Real.log (-lowerLambertW x) = Real.log (1 / (-x)) := by
  have hW := lowerLambertW_mul_exp hx
  have hWneg : lowerLambertW x < -1 := lowerLambertW_lt_neg_one hx
  have hy : 0 < -lowerLambertW x := by linarith
  have hx0 : 0 < -x := by linarith [hx.2]
  -- `-x = (-W) · exp W`, so `log (-x) = log (-W) + W`
  have hprod : -x = (-lowerLambertW x) * Real.exp (lowerLambertW x) := by linarith
  have hlog : Real.log (-x) = Real.log (-lowerLambertW x) + lowerLambertW x := by
    rw [hprod, Real.log_mul hy.ne' (Real.exp_pos _).ne', Real.log_exp]
  rw [one_div, Real.log_inv, hlog]
  ring

/-- **Near-zero logarithmic bounds, upper half.**  For `-1/e < x < 0` and
`η = log (1 / (-x))`, `W₋₁(x) < -η - log η`. -/
theorem lowerLambertW_lt_neg_log_sub {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    lowerLambertW x <
      -Real.log (1 / (-x)) - Real.log (Real.log (1 / (-x))) := by
  have hy : 1 < -lowerLambertW x := by linarith [lowerLambertW_lt_neg_one hx]
  have := SubLog.lt_of_sub_log_eq hy (neg_lowerLambertW_sub_log_eq hx)
  linarith

/-- **Near-zero logarithmic bounds, lower half.**  For `-1/e < x < 0` and
`η = log (1 / (-x))`, `-η - η·log η / (η - 1) ≤ W₋₁(x)`. -/
theorem neg_log_sub_div_le_lowerLambertW {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    -Real.log (1 / (-x)) -
        Real.log (1 / (-x)) * Real.log (Real.log (1 / (-x))) / (Real.log (1 / (-x)) - 1) ≤
      lowerLambertW x := by
  have hy : 1 < -lowerLambertW x := by linarith [lowerLambertW_lt_neg_one hx]
  have := SubLog.le_of_sub_log_eq hy (neg_lowerLambertW_sub_log_eq hx)
  linarith

/-- **The two-sided near-zero bracket** for the lower branch, in the guide's
form: with `η = log (1 / (-x)) > 1`,
`-η - η·log η / (η - 1) ≤ W₋₁(x) < -η - log η`. -/
theorem lowerLambertW_near_zero_bounds {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    -Real.log (1 / (-x)) -
        Real.log (1 / (-x)) * Real.log (Real.log (1 / (-x))) / (Real.log (1 / (-x)) - 1) ≤
      lowerLambertW x ∧
    lowerLambertW x < -Real.log (1 / (-x)) - Real.log (Real.log (1 / (-x))) :=
  ⟨neg_log_sub_div_le_lowerLambertW hx, lowerLambertW_lt_neg_log_sub hx⟩

/-- The auxiliary quantity `η = log (1 / (-x))` exceeds `1` on `(-1/e, 0)`. -/
theorem one_lt_log_one_div_neg {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    1 < Real.log (1 / (-x)) := by
  have hx0 : 0 < -x := by linarith [hx.2]
  have hlt : -x < Real.exp (-1) := by linarith [hx.1]
  rw [one_div, Real.log_inv]
  have := Real.log_lt_log hx0 hlt
  rw [Real.log_exp] at this
  linarith

end Fabius
