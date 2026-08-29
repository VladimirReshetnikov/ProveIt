import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Multiple-angle domination bounds for sine and cosine

Two elementary inequalities that bound an `m`-fold angle by the
single angle, with no constant beyond `m` itself:

`|sin (m x)| ≤ m·|sin x|` for **every** natural `m`, and
`|cos (m x)| ≤ m·|cos x|` for every **odd** natural `m`.

They are the crude but unconditional companions of the exact
multiple-angle identities used throughout the dyadic sine-product
theory: whenever a dilated factor `sin (m·π t)` has to be compared
with the base factor `sin (π t)` — or a cosine detector `cos (m·π t)`
with `cos (π t)` — this is the inequality that does it, turning
"the base factor is small" into "the dilated factor is small" with a
completely explicit linear loss.

* `abs_sin_nat_mul_le` — the **sine bound**: `|sin (m x)| ≤ m·|sin x|`
  for every `m : ℕ` and every `x : ℝ`.  Induction on `m` through
  `sin ((n+1) x) = sin (n x)·cos x + cos (n x)·sin x`, discarding each
  cosine factor by `|cos| ≤ 1`.
* `abs_cos_odd_mul_le` — the **cosine bound in odd-index form**:
  `|cos ((2k+1) x)| ≤ (2k+1)·|cos x|` for every `k : ℕ`.  Induction in
  steps of two along the Chebyshev three-term recursion
  `cos ((a+2) x) = 2·cos ((a+1) x)·cos x - cos (a x)`, discarding the
  interior cosine by `|cos| ≤ 1`; the base case `k = 0` is an
  equality.
* `abs_cos_nat_mul_le_of_odd` — the same bound packaged for an
  arbitrary `m : ℕ` carrying `Odd m`.
* `sin_nat_mul_eq_zero_of_sin_eq_zero` and
  `cos_nat_mul_eq_zero_of_cos_eq_zero` — the zero-transfer
  corollaries: a zero of the base factor forces a zero of the dilated
  factor (for the cosine, only along odd dilations).
* `not_abs_cos_two_mul_le` — the parity hypothesis is genuinely
  needed: at `x = π/2` the even multiplier `m = 2` violates the
  cosine bound, since `cos π = -1` while `cos (π/2) = 0`.

The sine bound needs no parity hypothesis because the zero set `πℤ`
of `sin` is stable under every dilation `x ↦ m x`; the cosine bound
does need one, because the zero set `π/2 + πℤ` of `cos` is stable
only under the odd dilations.  Oddness is used nowhere else: the
whole content is the two-step recursion, and the parity only chooses
the arithmetic progression `1, 3, 5, …` on which the induction runs.
-/

set_option autoImplicit false

open Real

namespace Fabius

/-- **The sine multiple-angle bound**: for every natural `m` and every
real `x`, `|sin (m x)| ≤ m·|sin x|`.  No parity hypothesis is needed:
the zero set of `sin` is `πℤ`, which every dilation preserves. -/
theorem abs_sin_nat_mul_le (m : ℕ) (x : ℝ) :
    |Real.sin ((m : ℝ) * x)| ≤ (m : ℝ) * |Real.sin x| := by
  induction m with
  | zero => simp
  | succ n ih =>
      have key : |Real.sin ((n : ℝ) * x + x)| ≤
          (n : ℝ) * |Real.sin x| + |Real.sin x| := by
        rw [Real.sin_add]
        refine (abs_add_le _ _).trans ?_
        have hA : |Real.sin ((n : ℝ) * x) * Real.cos x| ≤
            (n : ℝ) * |Real.sin x| := by
          rw [abs_mul]
          refine le_trans ?_ ih
          calc |Real.sin ((n : ℝ) * x)| * |Real.cos x|
              ≤ |Real.sin ((n : ℝ) * x)| * 1 :=
                mul_le_mul_of_nonneg_left (Real.abs_cos_le_one x)
                  (abs_nonneg _)
            _ = |Real.sin ((n : ℝ) * x)| := mul_one _
        have hB : |Real.cos ((n : ℝ) * x) * Real.sin x| ≤
            1 * |Real.sin x| := by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right
            (Real.abs_cos_le_one ((n : ℝ) * x)) (abs_nonneg _)
        refine (add_le_add hA hB).trans ?_
        exact le_of_eq (by ring)
      have hx : (n : ℝ) * x + x = ((n + 1 : ℕ) : ℝ) * x := by
        push_cast
        ring
      have hc : (n : ℝ) * |Real.sin x| + |Real.sin x| =
          ((n + 1 : ℕ) : ℝ) * |Real.sin x| := by
        push_cast
        ring
      rw [hx, hc] at key
      exact key

/-- Zero transfer for the sine: if `sin x = 0` then `sin (m x) = 0`
for every natural `m`.  Immediate from `abs_sin_nat_mul_le`. -/
theorem sin_nat_mul_eq_zero_of_sin_eq_zero (m : ℕ) {x : ℝ}
    (hx : Real.sin x = 0) : Real.sin ((m : ℝ) * x) = 0 := by
  have h := abs_sin_nat_mul_le m x
  rw [hx, abs_zero, mul_zero] at h
  exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))

/-- The Chebyshev three-term recursion in the additive form used
below: `cos ((a+2) x) = 2·cos ((a+1) x)·cos x + (-cos (a x))`, an
identity for all real `a` and `x`.  It is the product-to-sum formula
`cos (u + x) + cos (u - x) = 2·cos u·cos x` at `u = (a+1) x`. -/
private theorem cos_add_two_mul (a x : ℝ) :
    Real.cos ((a + 2) * x) =
      2 * Real.cos ((a + 1) * x) * Real.cos x +
        -Real.cos (a * x) := by
  have h1 : Real.cos ((a + 2) * x) =
      Real.cos ((a + 1) * x) * Real.cos x -
        Real.sin ((a + 1) * x) * Real.sin x := by
    rw [show (a + 2) * x = (a + 1) * x + x by ring, Real.cos_add]
  have h2 : Real.cos (a * x) =
      Real.cos ((a + 1) * x) * Real.cos x +
        Real.sin ((a + 1) * x) * Real.sin x := by
    rw [show a * x = (a + 1) * x - x by ring, Real.cos_sub]
  rw [h1, h2]
  ring

/-- `|2·cos u| ≤ 2`, for every real `u`. -/
private theorem abs_two_mul_cos_le (u : ℝ) :
    |2 * Real.cos u| ≤ 2 := by
  rw [abs_mul, abs_two]
  have h : |Real.cos u| ≤ 1 := Real.abs_cos_le_one u
  linarith

/-- The interior term of the Chebyshev step costs exactly a factor
`2`: `|2·cos u·cos x| ≤ 2·|cos x|`. -/
private theorem abs_two_mul_cos_mul_cos_le (u x : ℝ) :
    |2 * Real.cos u * Real.cos x| ≤ 2 * |Real.cos x| := by
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (abs_two_mul_cos_le u)
    (abs_nonneg _)

/-- One Chebyshev step of the cosine bound: the estimate at the real
multiplier `a` propagates to the multiplier `a + 2`.  The step is
where the two-step structure — hence, downstream, the parity — lives;
the statement itself holds for an arbitrary real `a`. -/
private theorem abs_cos_add_two_mul_le (a x : ℝ)
    (ha : |Real.cos (a * x)| ≤ a * |Real.cos x|) :
    |Real.cos ((a + 2) * x)| ≤ (a + 2) * |Real.cos x| := by
  rw [cos_add_two_mul]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg]
  refine (add_le_add
    (abs_two_mul_cos_mul_cos_le ((a + 1) * x) x) ha).trans ?_
  exact le_of_eq (by ring)

/-- **The cosine multiple-angle bound, odd-index form**: for every
`k : ℕ` and every real `x`, `|cos ((2k+1) x)| ≤ (2k+1)·|cos x|`.
Induction in steps of two from the base case `k = 0`, which is an
equality. -/
theorem abs_cos_odd_mul_le (k : ℕ) (x : ℝ) :
    |Real.cos (((2 * k + 1 : ℕ) : ℝ) * x)| ≤
      ((2 * k + 1 : ℕ) : ℝ) * |Real.cos x| := by
  induction k with
  | zero => simp
  | succ n ih =>
      have h := abs_cos_add_two_mul_le (((2 * n + 1 : ℕ) : ℝ)) x ih
      have hx : (((2 * n + 1 : ℕ) : ℝ) + 2) * x =
          ((2 * (n + 1) + 1 : ℕ) : ℝ) * x := by
        push_cast
        ring
      have hc : (((2 * n + 1 : ℕ) : ℝ) + 2) * |Real.cos x| =
          ((2 * (n + 1) + 1 : ℕ) : ℝ) * |Real.cos x| := by
        push_cast
        ring
      rw [hx, hc] at h
      exact h

/-- **The cosine multiple-angle bound**: for every **odd** natural `m`
and every real `x`, `|cos (m x)| ≤ m·|cos x|`.  Oddness is used only
to write `m = 2k+1` and start the two-step induction; the bound is
false for even `m`, see `not_abs_cos_two_mul_le`. -/
theorem abs_cos_nat_mul_le_of_odd {m : ℕ} (hm : Odd m) (x : ℝ) :
    |Real.cos ((m : ℝ) * x)| ≤ (m : ℝ) * |Real.cos x| := by
  obtain ⟨k, rfl⟩ := hm
  exact abs_cos_odd_mul_le k x

/-- Zero transfer for the cosine along odd dilations: if `cos x = 0`
and `m` is odd then `cos (m x) = 0`.  Equivalently, the zero set
`π/2 + πℤ` of `cos` is stable under every odd dilation. -/
theorem cos_nat_mul_eq_zero_of_cos_eq_zero {m : ℕ} (hm : Odd m)
    {x : ℝ} (hx : Real.cos x = 0) : Real.cos ((m : ℝ) * x) = 0 := by
  have h := abs_cos_nat_mul_le_of_odd hm x
  rw [hx, abs_zero, mul_zero] at h
  exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))

/-- **Oddness is necessary**: the cosine bound fails for the even
multiplier `m = 2` at `x = π/2`, where `|cos π| = 1` while
`2·|cos (π/2)| = 0`.  So there is no analogue of
`abs_sin_nat_mul_le` for the cosine without a parity hypothesis. -/
theorem not_abs_cos_two_mul_le :
    ¬ |Real.cos (((2 : ℕ) : ℝ) * (π / 2))| ≤
        ((2 : ℕ) : ℝ) * |Real.cos (π / 2)| := by
  have harg : ((2 : ℕ) : ℝ) * (π / 2) = π := by
    push_cast
    ring
  rw [harg, Real.cos_pi, Real.cos_pi_div_two]
  norm_num

end Fabius
