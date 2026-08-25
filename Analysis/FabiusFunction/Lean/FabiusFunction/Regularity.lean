import FabiusFunction.Differential
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Sharp Lipschitz regularity of the Fabius and Rvachev functions

The single global differential equation `F'(x) = 2 up(2x - 1)` of
`FabiusFunction.Differential` bounds the derivative of the bounded Fabius
function by `2` everywhere, because `up` takes values in `[0,1]`.  This file
records the resulting global Lipschitz estimates together with a proof that
the constant `2` is optimal: the derivative attains the value `2` at the
midpoint `1/2`, where `up(2x-1) = up(0) = 1`.

Two consequences are stated separately because they are used as quantitative
input elsewhere: the linear majorant `F(x) ≤ 2x` at the left endpoint (with
its reflection at the right endpoint) and the linear majorant
`up(x) ≤ 2(1 - |x|)` at the two ends of the support of Rvachev's function.
The first removes the hypothesis `x ≤ 1/2` carried by an auxiliary estimate
used elsewhere in the development; the content is on `[0, 1/2]`, since for
`x ≥ 1/2` the bound is just `F(x) ≤ 1 ≤ 2x`.

For convenient global use, each endpoint estimate also has a version in which
the signed distance is replaced by its nonnegative truncation `max d 0`.
Those forms have no interval hypothesis and remain meaningful outside the
support.
-/

set_option autoImplicit false

open Set

namespace Fabius

/-! ## Global Lipschitz bounds -/

/-- The bounded Fabius function is `2`-Lipschitz on all of `ℝ`. -/
theorem lipschitzWith_fabiusReal (F : BoundedFabius) (hF : IsFabius F) :
    LipschitzWith 2 (fabiusReal F) := by
  refine lipschitzWith_of_nnnorm_deriv_le (fabius_differentiable F hF) fun x => ?_
  have h0 := rvachevUp_nonneg F (2 * x - 1)
  have h1 := rvachevUp_le_one F (2 * x - 1)
  have hb : ‖deriv (fabiusReal F) x‖ ≤ (2 : ℝ) := by
    rw [(fabius_hasDerivAt F hF x).deriv, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * rvachevUp F (2 * x - 1))]
    linarith
  exact_mod_cast hb

/-- Rvachev's up function is `2`-Lipschitz on all of `ℝ`. -/
theorem lipschitzWith_rvachevUp (F : BoundedFabius) (hF : IsFabius F) :
    LipschitzWith 2 (rvachevUp F) := by
  refine lipschitzWith_of_nnnorm_deriv_le
    (fun x => (rvachev_hasDerivAt F hF x).differentiableAt) fun x => ?_
  have h0 := rvachevUp_nonneg F (2 * x + 1)
  have h1 := rvachevUp_le_one F (2 * x + 1)
  have h2 := rvachevUp_nonneg F (2 * x - 1)
  have h3 := rvachevUp_le_one F (2 * x - 1)
  have hb : ‖deriv (rvachevUp F) x‖ ≤ (2 : ℝ) := by
    rw [(rvachev_hasDerivAt F hF x).deriv, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  exact_mod_cast hb

/-- Explicit form of the Lipschitz estimate for the bounded Fabius function. -/
theorem abs_fabiusReal_sub_le (F : BoundedFabius) (hF : IsFabius F) (x y : ℝ) :
    |fabiusReal F x - fabiusReal F y| ≤ 2 * |x - y| := by
  have h := (lipschitzWith_fabiusReal F hF).dist_le_mul x y
  simpa [Real.dist_eq] using h

/-- Explicit form of the Lipschitz estimate for Rvachev's up function. -/
theorem abs_rvachevUp_sub_le (F : BoundedFabius) (hF : IsFabius F) (x y : ℝ) :
    |rvachevUp F x - rvachevUp F y| ≤ 2 * |x - y| := by
  have h := (lipschitzWith_rvachevUp F hF).dist_le_mul x y
  simpa [Real.dist_eq] using h

/-! ## Optimality of the constant -/

/-- No Lipschitz constant smaller than `2` works for the bounded Fabius
function: its derivative equals `2` at the midpoint. -/
theorem two_le_of_lipschitzWith_fabiusReal (F : BoundedFabius) (hF : IsFabius F)
    {K : NNReal} (hK : LipschitzWith K (fabiusReal F)) : (2 : ℝ) ≤ (K : ℝ) := by
  have hd := fabius_hasDerivAt F hF (1 / 2 : ℝ)
  rw [show 2 * (1 / 2 : ℝ) - 1 = 0 by norm_num, rvachevUp_zero F hF,
    mul_one] at hd
  have h2 := hd.le_of_lipschitz hK
  rwa [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h2

/-- No Lipschitz constant smaller than `2` works for Rvachev's up function:
its derivative equals `-2` at the midpoint of the right half of the support. -/
theorem two_le_of_lipschitzWith_rvachevUp (F : BoundedFabius) (hF : IsFabius F)
    {K : NNReal} (hK : LipschitzWith K (rvachevUp F)) : (2 : ℝ) ≤ (K : ℝ) := by
  have hd := rvachev_hasDerivAt F hF (1 / 2 : ℝ)
  rw [show 2 * (1 / 2 : ℝ) + 1 = 2 by norm_num,
    show 2 * (1 / 2 : ℝ) - 1 = 0 by norm_num,
    rvachevUp_eq_zero_of_one_le F hF (by norm_num : (1 : ℝ) ≤ 2),
    rvachevUp_zero F hF, show (2 : ℝ) * (0 - 1) = -2 by norm_num] at hd
  have h2 := hd.le_of_lipschitz hK
  rwa [Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h2

/-- `2` is the least Lipschitz constant of the bounded Fabius function. -/
theorem isLeast_lipschitzWith_fabiusReal (F : BoundedFabius) (hF : IsFabius F) :
    IsLeast {K : NNReal | LipschitzWith K (fabiusReal F)} 2 := by
  refine ⟨lipschitzWith_fabiusReal F hF, fun K hK => ?_⟩
  exact_mod_cast two_le_of_lipschitzWith_fabiusReal F hF hK

/-- `2` is the least Lipschitz constant of Rvachev's up function. -/
theorem isLeast_lipschitzWith_rvachevUp (F : BoundedFabius) (hF : IsFabius F) :
    IsLeast {K : NNReal | LipschitzWith K (rvachevUp F)} 2 := by
  refine ⟨lipschitzWith_rvachevUp F hF, fun K hK => ?_⟩
  exact_mod_cast two_le_of_lipschitzWith_rvachevUp F hF hK

/-! ## Linear majorants at the endpoints -/

/-- The bounded Fabius function is dominated by `2x` on the whole half line
`[0, ∞)`.  On `[1/2, ∞)` this is the trivial bound `F ≤ 1 ≤ 2x`; the content
is on `[0, 1/2]`. -/
theorem fabiusReal_le_two_mul (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx : 0 ≤ x) : fabiusReal F x ≤ 2 * x := by
  have h := abs_fabiusReal_sub_le F hF x 0
  rw [hF.zero_of_nonpos 0 le_rfl, sub_zero, sub_zero, abs_of_nonneg hx] at h
  exact (le_abs_self _).trans h

/-- Reflected linear majorant at the right endpoint of the unit interval. -/
theorem one_sub_fabiusReal_le_two_mul (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx : x ≤ 1) : 1 - fabiusReal F x ≤ 2 * (1 - x) := by
  have h := fabiusReal_le_two_mul F hF (x := 1 - x) (by linarith)
  rwa [hF.symmetry_all x] at h

/-- Rvachev's up function vanishes at least linearly at the two ends of its
support. -/
theorem rvachevUp_le_two_mul_one_sub_abs (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (hx : |x| ≤ 1) : rvachevUp F x ≤ 2 * (1 - |x|) := by
  have key : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → rvachevUp F y ≤ 2 * (1 - y) := by
    intro y hy0 hy1
    rcases eq_or_lt_of_le hy0 with hy | hy
    · rw [← hy, rvachevUp_zero F hF]
      norm_num
    · rw [rvachevUp_of_pos F hy]
      exact fabiusReal_le_two_mul F hF (by linarith)
  by_cases hx0 : 0 ≤ x
  · rw [abs_of_nonneg hx0]
    exact key x hx0 (by rwa [abs_of_nonneg hx0] at hx)
  · have hneg : x < 0 := lt_of_not_ge hx0
    rw [abs_of_neg hneg, ← rvachevUp_even F x]
    exact key (-x) (by linarith) (by rw [abs_of_neg hneg] at hx; linarith)

/-! ### Global truncated-distance forms -/

/-- Hypothesis-free linear majorant at the origin, using the nonnegative
truncation of the distance to the endpoint. -/
theorem fabiusReal_le_two_mul_max (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) : fabiusReal F x ≤ 2 * max x 0 := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx]
    exact fabiusReal_le_two_mul F hF hx
  · have hxle : x ≤ 0 := (lt_of_not_ge hx).le
    rw [hF.zero_of_nonpos x hxle, max_eq_right hxle, mul_zero]

/-- Hypothesis-free reflected linear majorant at the right endpoint. -/
theorem one_sub_fabiusReal_le_two_mul_max (F : BoundedFabius)
    (hF : IsFabius F) (x : ℝ) :
    1 - fabiusReal F x ≤ 2 * max (1 - x) 0 := by
  by_cases hx : x ≤ 1
  · rw [max_eq_left (sub_nonneg.mpr hx)]
    exact one_sub_fabiusReal_le_two_mul F hF hx
  · have hxge : 1 ≤ x := (lt_of_not_ge hx).le
    rw [hF.one_of_one_le x hxge, sub_self,
      max_eq_right (sub_nonpos.mpr hxge), mul_zero]

/-- Global linear vanishing bound for Rvachev's function, with the distance
to the boundary truncated to zero outside its support. -/
theorem rvachevUp_le_two_mul_max_one_sub_abs (F : BoundedFabius)
    (hF : IsFabius F) (x : ℝ) :
    rvachevUp F x ≤ 2 * max (1 - |x|) 0 := by
  by_cases hx : |x| ≤ 1
  · rw [max_eq_left (sub_nonneg.mpr hx)]
    exact rvachevUp_le_two_mul_one_sub_abs F hF x hx
  · have houtside : x ∉ Ioo (-1 : ℝ) 1 := by
      intro hmem
      have habs : |x| < 1 := abs_lt.mpr ⟨hmem.1, hmem.2⟩
      exact hx habs.le
    have habs : 1 ≤ |x| := (lt_of_not_ge hx).le
    rw [rvachevUp_eq_zero_of_not_mem_Ioo F hF houtside,
      max_eq_right (sub_nonpos.mpr habs), mul_zero]

end Fabius
