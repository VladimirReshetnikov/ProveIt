import FabiusFunction.MultipleAngleBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Relative dominance of `sinc` under natural dilations

The multiple-angle bound `|sin (m x)| ≤ m·|sin x|` of
`MultipleAngleBounds` carries an explicit linear loss `m`.  Divided
by the argument, that loss disappears completely: the *normalized*
factor obeys

`|sinc (m x)| ≤ |sinc x|`   for every natural `m ≥ 1`,

with constant `1`.  The `m` gained in the numerator by the
multiple-angle bound is exactly the `m` lost in the denominator by
the dilation, so the dilated sinc factor never exceeds the base one
in absolute value.  This is the relative-dominance statement the
comb/defect layer wants when a table of dilated values `Φ(q·l/2)`,
`l` odd, has to be dominated by the base value `Φ(q/2)`: the
admissible factor is `1`, not `l`.

Three features of the statement are genuinely necessary, and each is
witnessed by a counterexample below.

* `m ≥ 1` cannot be dropped.  For `m = 0` the left side is
  `|sinc 0| = 1`, and the right side vanishes at `x = π`
  (`not_abs_sinc_zero_mul_le`).
* The multiplier must be an *integer*, not merely a real number
  `≥ 1`.  At the multiplier `3/2` and `x = π` the base factor
  vanishes while the dilated one does not
  (`not_abs_sinc_three_halves_mul_le`).  The reason is structural:
  the zero set `πℤ \ {0}` of `sinc` is stable under integer
  dilations only.
* The absolute values cannot be removed.  At `m = 2` and
  `x = 3π/2` the base factor is negative and the dilated one is `0`
  (`not_sinc_two_mul_le`).

Unlike the cosine bound of `MultipleAngleBounds`, **no parity
hypothesis is needed** here — the sine's zero set `πℤ` is stable
under every dilation.  The odd-`l` product statement asked for by
the comb layer is therefore recorded as a corollary of a strictly
stronger `1 ≤ l` statement.

## Main declarations

* `abs_sinc_nat_mul_le` — **the relative dominance bound**:
  `1 ≤ m → |sinc (m x)| ≤ |sinc x|` for `m : ℕ` and `x : ℝ`.
* `prod_abs_sinc_nat_mul_le` — the termwise consequence over an
  arbitrary `Finset`: dilating every argument by a fixed `m ≥ 1`
  cannot increase the product of `|sinc|`.
* `prod_abs_sinc_dilate_le` — the **dyadic product form**: for
  `1 ≤ l`,
  `∏_{n<N} |sinc (l·t/2ⁿ)| ≤ ∏_{n<N} |sinc (t/2ⁿ)|`.
* `prod_abs_sinc_odd_dilate_le` — the same for odd `l`, the shape
  used by the first-defect tables.
* `sinc_eq_zero_iff` — `sinc x = 0 ↔ x ≠ 0 ∧ sin x = 0`.
* `sinc_nat_mul_eq_zero_of_sinc_eq_zero` and
  `sinc_ne_zero_of_sinc_nat_mul_ne_zero` — zero transfer along
  natural dilations, and its contrapositive.
* `not_abs_sinc_zero_mul_le`, `not_abs_sinc_three_halves_mul_le`,
  `not_sinc_two_mul_le` — the three sharpness witnesses.
-/

set_option autoImplicit false

open Real

namespace Fabius

/-! ## The relative dominance bound -/

/-- **Relative dominance of the base sinc factor**: for every natural
`m ≥ 1` and every real `x`,

`|sinc (m x)| ≤ |sinc x|`.

At `x = 0` both sides equal `1`.  For `x ≠ 0` the argument `m x` is
again nonzero, and

`|sinc (m x)| = |sin (m x)| / (m|x|) ≤ m|sin x| / (m|x|) = |sinc x|`

by `abs_sin_nat_mul_le`; the factor `m` supplied by the
multiple-angle bound cancels against the factor `m` produced by the
dilated denominator, leaving constant `1`.  The hypothesis `1 ≤ m`
is essential, see `not_abs_sinc_zero_mul_le`. -/
theorem abs_sinc_nat_mul_le {m : ℕ} (hm : 1 ≤ m) (x : ℝ) :
    |Real.sinc ((m : ℝ) * x)| ≤ |Real.sinc x| := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hm' : 0 < m := by omega
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm'
    have hmx : (m : ℝ) * x ≠ 0 := mul_ne_zero (ne_of_gt hmpos) hx
    have hxpos : (0 : ℝ) < |x| := abs_pos.mpr hx
    have hden : |(m : ℝ) * x| = (m : ℝ) * |x| := by
      rw [abs_mul, Nat.abs_cast]
    have hdenpos : (0 : ℝ) < (m : ℝ) * |x| := mul_pos hmpos hxpos
    rw [Real.sinc_of_ne_zero hmx, Real.sinc_of_ne_zero hx, abs_div,
      abs_div, hden, div_le_div_iff₀ hdenpos hxpos]
    calc |Real.sin ((m : ℝ) * x)| * |x|
        ≤ ((m : ℝ) * |Real.sin x|) * |x| :=
          mul_le_mul_of_nonneg_right (abs_sin_nat_mul_le m x)
            (abs_nonneg x)
      _ = |Real.sin x| * ((m : ℝ) * |x|) := by ring

/-! ## Products of dilated factors -/

/-- **Termwise dominance in a product**: dilating every argument of a
finite `|sinc|` product by one and the same natural `m ≥ 1` cannot
increase the product.  Immediate from `abs_sinc_nat_mul_le` and
`Finset.prod_le_prod`, the terms being nonnegative. -/
theorem prod_abs_sinc_nat_mul_le {ι : Type*} {m : ℕ} (hm : 1 ≤ m)
    (s : Finset ι) (f : ι → ℝ) :
    ∏ i ∈ s, |Real.sinc ((m : ℝ) * f i)| ≤
      ∏ i ∈ s, |Real.sinc (f i)| :=
  Finset.prod_le_prod (fun _ _ => abs_nonneg _)
    (fun i _ => abs_sinc_nat_mul_le hm (f i))

/-- **The dyadic dilated product is dominated**: for every natural
`l ≥ 1`, every real `t` and every `N`,

`∏_{n<N} |sinc (l·t/2ⁿ)| ≤ ∏_{n<N} |sinc (t/2ⁿ)|`.

The dilation commutes with the dyadic scaling,
`l·t/2ⁿ = l·(t/2ⁿ)`, so `abs_sinc_nat_mul_le` applies factor by
factor.  Note that no parity hypothesis on `l` appears: only
`1 ≤ l` is used. -/
theorem prod_abs_sinc_dilate_le {l : ℕ} (hl : 1 ≤ l) (t : ℝ)
    (N : ℕ) :
    ∏ n ∈ Finset.range N, |Real.sinc ((l : ℝ) * t / 2 ^ n)| ≤
      ∏ n ∈ Finset.range N, |Real.sinc (t / 2 ^ n)| := by
  refine Finset.prod_le_prod (fun _ _ => abs_nonneg _)
    (fun n _ => ?_)
  have h := abs_sinc_nat_mul_le hl (t / 2 ^ n)
  rw [← mul_div_assoc] at h
  exact h

/-- **The odd-dilation form used by the first-defect tables**: for
odd `l`, the dilated dyadic product is dominated by the base one.
A special case of `prod_abs_sinc_dilate_le`, oddness entering only
through `l ≥ 1`. -/
theorem prod_abs_sinc_odd_dilate_le {l : ℕ} (hl : Odd l) (t : ℝ)
    (N : ℕ) :
    ∏ n ∈ Finset.range N, |Real.sinc ((l : ℝ) * t / 2 ^ n)| ≤
      ∏ n ∈ Finset.range N, |Real.sinc (t / 2 ^ n)| := by
  obtain ⟨k, rfl⟩ := hl
  refine prod_abs_sinc_dilate_le ?_ t N
  omega

/-! ## The zero set -/

/-- The zero set of `sinc`: `sinc x = 0` exactly when `x ≠ 0` and
`sin x = 0`, i.e. on `πℤ \ {0}`.  The origin is excluded by the
normalization `sinc 0 = 1`. -/
theorem sinc_eq_zero_iff {x : ℝ} :
    Real.sinc x = 0 ↔ x ≠ 0 ∧ Real.sin x = 0 := by
  constructor
  · intro h
    rcases eq_or_ne x 0 with rfl | hx
    · rw [Real.sinc_zero] at h
      exact absurd h one_ne_zero
    · refine ⟨hx, ?_⟩
      rw [Real.sinc_of_ne_zero hx, div_eq_zero_iff] at h
      exact h.resolve_right hx
  · rintro ⟨hx, hs⟩
    rw [Real.sinc_of_ne_zero hx, hs, zero_div]

/-- **Zero transfer along natural dilations**: if the base factor
vanishes then so does every dilated factor `sinc (m x)` with
`m ≥ 1`.  Read off from `abs_sinc_nat_mul_le`, whose right-hand side
is then `0`.  Equivalently, the zero set `πℤ \ {0}` of `sinc` is
stable under every dilation by a positive integer. -/
theorem sinc_nat_mul_eq_zero_of_sinc_eq_zero {m : ℕ} (hm : 1 ≤ m)
    {x : ℝ} (hx : Real.sinc x = 0) :
    Real.sinc ((m : ℝ) * x) = 0 := by
  have h := abs_sinc_nat_mul_le hm x
  rw [hx, abs_zero] at h
  exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))

/-- The contrapositive of `sinc_nat_mul_eq_zero_of_sinc_eq_zero`: a
nonvanishing dilated factor forces a nonvanishing base factor. -/
theorem sinc_ne_zero_of_sinc_nat_mul_ne_zero {m : ℕ} (hm : 1 ≤ m)
    {x : ℝ} (h : Real.sinc ((m : ℝ) * x) ≠ 0) :
    Real.sinc x ≠ 0 := fun hx =>
  h (sinc_nat_mul_eq_zero_of_sinc_eq_zero hm hx)

/-! ## Sharpness -/

/-- `sinc` vanishes at `π`; recorded once for the three
counterexamples below. -/
private theorem sinc_pi_eq_zero : Real.sinc Real.pi = 0 := by
  rw [Real.sinc_of_ne_zero Real.pi_pos.ne', Real.sin_pi, zero_div]

/-- **`m ≥ 1` is necessary**: the dominance bound fails for the
multiplier `m = 0` at `x = π`, where the left side is
`|sinc 0| = 1` while the right side is `|sinc π| = 0`.  So no
statement of the form `|sinc (m x)| ≤ |sinc x|` can hold for all
naturals `m`. -/
theorem not_abs_sinc_zero_mul_le :
    ¬ |Real.sinc (((0 : ℕ) : ℝ) * Real.pi)| ≤
        |Real.sinc Real.pi| := by
  rw [Nat.cast_zero, zero_mul, Real.sinc_zero, sinc_pi_eq_zero,
    abs_zero, abs_one, not_le]
  norm_num

/-- **The multiplier must be an integer**: the dominance bound fails
for the real multiplier `3/2` at `x = π`, where `sinc π = 0` while
`sinc (3π/2) = -1/(3π/2) ≠ 0`.  The zero set `πℤ \ {0}` of `sinc`
is stable under integer dilations only, so `abs_sinc_nat_mul_le`
has no analogue for real multipliers `≥ 1`. -/
theorem not_abs_sinc_three_halves_mul_le :
    ¬ |Real.sinc ((3 / 2 : ℝ) * Real.pi)| ≤
        |Real.sinc Real.pi| := by
  have hne : (3 / 2 : ℝ) * Real.pi ≠ 0 := by positivity
  have hd : (0 : ℝ) < (3 / 2 : ℝ) * Real.pi := by positivity
  have hsin : Real.sin ((3 / 2 : ℝ) * Real.pi) = -1 := by
    rw [show (3 / 2 : ℝ) * Real.pi = Real.pi / 2 + Real.pi by ring,
      Real.sin_add_pi, Real.sin_pi_div_two]
  have hL : Real.sinc ((3 / 2 : ℝ) * Real.pi) =
      -1 / ((3 / 2 : ℝ) * Real.pi) := by
    rw [Real.sinc_of_ne_zero hne, hsin]
  have hneg : (-1 : ℝ) / ((3 / 2 : ℝ) * Real.pi) < 0 :=
    div_neg_of_neg_of_pos (by norm_num) hd
  rw [hL, sinc_pi_eq_zero, abs_zero, not_le, abs_pos]
  exact ne_of_lt hneg

/-- **The absolute values are necessary**: the unsigned comparison
`sinc (m x) ≤ sinc x` fails already at `m = 2`, `x = 3π/2`, where
the base factor `sinc (3π/2) = -1/(3π/2)` is negative while the
dilated factor `sinc (3π) = 0` is not.  So `abs_sinc_nat_mul_le`
cannot be strengthened by deleting the absolute values. -/
theorem not_sinc_two_mul_le :
    ¬ Real.sinc (((2 : ℕ) : ℝ) * (3 * Real.pi / 2)) ≤
        Real.sinc (3 * Real.pi / 2) := by
  have hcast : ((3 : ℕ) : ℝ) = 3 := by norm_num
  have hs3 : Real.sin (3 * Real.pi) = 0 := by
    have h := sin_nat_mul_eq_zero_of_sin_eq_zero 3 Real.sin_pi
    rwa [hcast] at h
  have harg : ((2 : ℕ) : ℝ) * (3 * Real.pi / 2) = 3 * Real.pi := by
    push_cast
    ring
  have h3 : (3 * Real.pi : ℝ) ≠ 0 := by positivity
  have hL : Real.sinc (((2 : ℕ) : ℝ) * (3 * Real.pi / 2)) = 0 := by
    rw [harg, Real.sinc_of_ne_zero h3, hs3, zero_div]
  have hxne : (3 * Real.pi / 2 : ℝ) ≠ 0 := by positivity
  have hd : (0 : ℝ) < 3 * Real.pi / 2 := by positivity
  have hsin : Real.sin (3 * Real.pi / 2) = -1 := by
    rw [show (3 * Real.pi / 2 : ℝ) = Real.pi / 2 + Real.pi by ring,
      Real.sin_add_pi, Real.sin_pi_div_two]
  have hR : Real.sinc (3 * Real.pi / 2) =
      -1 / (3 * Real.pi / 2) := by
    rw [Real.sinc_of_ne_zero hxne, hsin]
  have hneg : (-1 : ℝ) / (3 * Real.pi / 2) < 0 :=
    div_neg_of_neg_of_pos (by norm_num) hd
  rw [hL, hR, not_le]
  exact hneg

end Fabius
