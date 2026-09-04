import FabiusFunction.PrincipalLambertW

/-!
# Square-root bounds for the principal branch on `(-1/e, 0)`

The Lambert W guide's "two square-root bounds and a linear bound": for
`-1/e < x < 0`,

`-1 + √(1 + e·x) < W₀(x) < -1 + √(2(1 + e·x))`,  and  `W₀(x) < x`.

## The mechanism

Put `W₀(x) = -1 + s` with `0 < s < 1`.  The defining equation gives
`1 + e·x = 1 + (s - 1)·eˢ`, so the two square-root bounds are the two
elementary exponential inequalities

* `eˢ > 1 + s`  (the tangent line), equivalent to `1 + (s-1)eˢ < s²`, and
* `eˢ(1 - s) < 1 - s²/2`  (the next Taylor term), equivalent to
  `s² < 2(1 + (s-1)eˢ)`.

The second is proved here from its derivative: `f(s) = 1 - s²/2 - eˢ(1-s)`
vanishes at `0` and has `f'(s) = s(eˢ - 1) > 0` on `(0, 1)`.  The linear bound
`W₀(x) < x` is just `W < W·e^W` for `-1 < W < 0`, where `e^W < 1`.
-/

set_option autoImplicit false

open Set

namespace Fabius

/-- **The second-order tangent inequality**: `eˢ(1 - s) < 1 - s²/2` for
`0 < s < 1`.  Its derivative form is `s(eˢ - 1) > 0`. -/
theorem exp_mul_one_sub_lt_one_sub_half_sq {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Real.exp s * (1 - s) < 1 - s ^ 2 / 2 := by
  -- `f t = 1 - t²/2 - eᵗ (1 - t)` is strictly increasing on `[0, 1]` from `f 0 = 0`
  let f : ℝ → ℝ := fun t => 1 - t ^ 2 / 2 - Real.exp t * (1 - t)
  have hderiv : ∀ t : ℝ, HasDerivAt f (t * (Real.exp t - 1)) t := by
    intro t
    -- the calculus lemmas return Pi-shaped functions, definitionally the ones
    -- named here; only the derivatives need `congr_deriv`
    have h1 : HasDerivAt (fun t : ℝ => 1 - t ^ 2 / 2) (-t) t :=
      (((hasDerivAt_pow 2 t).div_const 2).const_sub 1).congr_deriv (by norm_num <;> ring)
    have h2 : HasDerivAt (fun t : ℝ => Real.exp t * (1 - t))
        (Real.exp t * (1 - t) + Real.exp t * (-1)) t :=
      (Real.hasDerivAt_exp t).mul ((hasDerivAt_id t).const_sub 1)
    exact (h1.sub h2).congr_deriv (by ring)
  have hmono : StrictMonoOn f (Icc 0 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 1)
      (fun t _ => (hderiv t).continuousAt.continuousWithinAt) ?_
    intro t ht
    rw [interior_Icc, mem_Ioo] at ht
    rw [(hderiv t).deriv]
    have : 1 < Real.exp t := by
      have := Real.add_one_lt_exp ht.1.ne'
      linarith
    nlinarith
  have h0 : f 0 = 0 := by simp [f]
  have := hmono (mem_Icc.mpr ⟨le_rfl, zero_le_one⟩) (mem_Icc.mpr ⟨hs0.le, hs1.le⟩) hs0
  rw [h0] at this
  simp only [f] at this
  linarith

/-- On `(-1/e, 0)` the principal branch lies strictly in `(-1, 0)`. -/
theorem principalLambertW_mem_Ioo_of_neg {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    principalLambertW x ∈ Ioo (-1 : ℝ) 0 := by
  refine ⟨neg_one_lt_principalLambertW hx.1, ?_⟩
  have hle : principalLambertW x ≤ 0 := principalLambertW_nonpos ⟨hx.1.le, hx.2.le⟩
  refine lt_of_le_of_ne hle fun h0 => ?_
  have := principalLambertW_mul_exp hx.1.le
  rw [h0, zero_mul] at this
  exact hx.2.ne this.symm

/-- The defining equation in the shifted variable `s = W₀(x) + 1`:
`1 + e·x = 1 + (s - 1)·eˢ`. -/
theorem one_add_exp_one_mul_eq {x : ℝ} (hx : -Real.exp (-1) ≤ x) :
    1 + Real.exp 1 * x =
      1 + (principalLambertW x + 1 - 1) * Real.exp (principalLambertW x + 1) := by
  have h := principalLambertW_mul_exp hx
  have hx' : Real.exp 1 * x =
      Real.exp 1 * (principalLambertW x * Real.exp (principalLambertW x)) := by rw [h]
  rw [Real.exp_add, add_sub_cancel_right, hx']
  ring

/-- **The lower square-root bound**: for `-1/e < x < 0`,
`-1 + √(1 + e·x) < W₀(x)`. -/
theorem neg_one_add_sqrt_lt_principalLambertW {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    -1 + Real.sqrt (1 + Real.exp 1 * x) < principalLambertW x := by
  obtain ⟨hW0, hW1⟩ := principalLambertW_mem_Ioo_of_neg hx
  set s := principalLambertW x + 1 with hs
  have hs0 : 0 < s := by linarith
  have hs1 : s < 1 := by linarith
  have hkey : 1 + Real.exp 1 * x = 1 + (s - 1) * Real.exp s := one_add_exp_one_mul_eq hx.1.le
  -- `1 + (s-1)eˢ < s²`, i.e. `eˢ > 1 + s`
  have hexp : 1 + s < Real.exp s := by
    have := Real.add_one_lt_exp hs0.ne'
    linarith
  have hlt : 1 + Real.exp 1 * x < s ^ 2 := by
    rw [hkey]
    have hprod : (s - 1) * Real.exp s < (s - 1) * (1 + s) :=
      mul_lt_mul_of_neg_left hexp (by linarith)
    have hsq : (s - 1) * (1 + s) = s ^ 2 - 1 := by ring
    linarith
  -- `1 + e·x > 0` on the domain, so both square roots are honest
  have hnn : 0 ≤ 1 + Real.exp 1 * x := by
    have hE : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; simp
    have := mul_lt_mul_of_pos_left hx.1 (Real.exp_pos 1)
    nlinarith
  have := Real.sqrt_lt_sqrt hnn hlt
  rw [Real.sqrt_sq hs0.le] at this
  linarith

/-- **The upper square-root bound**: for `-1/e < x < 0`,
`W₀(x) < -1 + √(2(1 + e·x))`. -/
theorem principalLambertW_lt_neg_one_add_sqrt {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    principalLambertW x < -1 + Real.sqrt (2 * (1 + Real.exp 1 * x)) := by
  obtain ⟨hW0, hW1⟩ := principalLambertW_mem_Ioo_of_neg hx
  set s := principalLambertW x + 1 with hs
  have hs0 : 0 < s := by linarith
  have hs1 : s < 1 := by linarith
  have hkey : 1 + Real.exp 1 * x = 1 + (s - 1) * Real.exp s := one_add_exp_one_mul_eq hx.1.le
  -- `s² < 2(1 + (s-1)eˢ)`, i.e. `eˢ(1-s) < 1 - s²/2`
  have hlt : s ^ 2 < 2 * (1 + Real.exp 1 * x) := by
    rw [hkey]
    have h := exp_mul_one_sub_lt_one_sub_half_sq hs0 hs1
    have hflip : (s - 1) * Real.exp s = -(Real.exp s * (1 - s)) := by ring
    linarith
  have := (Real.lt_sqrt hs0.le).mpr hlt
  linarith

/-- **The linear bound**: for `-1/e < x < 0`, `W₀(x) < x`. -/
theorem principalLambertW_lt_self_of_neg {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    principalLambertW x < x := by
  obtain ⟨hW0, hW1⟩ := principalLambertW_mem_Ioo_of_neg hx
  have h := principalLambertW_mul_exp hx.1.le
  have he : Real.exp (principalLambertW x) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hW1
  -- `W·e^W - W = W·(e^W - 1)`, a product of two negatives
  have hpos : 0 < principalLambertW x * (Real.exp (principalLambertW x) - 1) :=
    mul_pos_of_neg_of_neg hW1 (by linarith)
  have hexp : principalLambertW x * (Real.exp (principalLambertW x) - 1) =
      principalLambertW x * Real.exp (principalLambertW x) - principalLambertW x := by ring
  linarith

/-- **The guide's negative-side bounds**, together: for `-1/e < x < 0`,
`-1 + √(1 + e·x) < W₀(x) < -1 + √(2(1 + e·x))` and `W₀(x) < x`. -/
theorem principalLambertW_negative_bounds {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    -1 + Real.sqrt (1 + Real.exp 1 * x) < principalLambertW x ∧
      principalLambertW x < -1 + Real.sqrt (2 * (1 + Real.exp 1 * x)) ∧
      principalLambertW x < x :=
  ⟨neg_one_add_sqrt_lt_principalLambertW hx, principalLambertW_lt_neg_one_add_sqrt hx,
    principalLambertW_lt_self_of_neg hx⟩

end Fabius
