import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Choose.Sum

/-!
# Exact polynomial moments of a dyadic tent

The Fabius and Rvachev up hierarchies are built by convolving
indicator functions; the first nontrivial member of that hierarchy is
the *tent* (hat) function

`tent c h x = max (1 - |x - c| / h) 0`,

the piecewise linear bump of half-width `h` centred at `c`.  This
module computes its polynomial moments exactly.  Neither Mathlib nor
the rest of the corpus carries any tent, hat or B-spline API, so the
two elementary integrals are built here directly from `integral_pow`.

The symmetric single-power integral carries the whole content.  On
`[0, h]` the profile `(1 - u/h)·uⁿ` is an honest polynomial, with
integral `h^(n+1)/(n+1) - h^(n+1)/(n+2) = h^(n+1)/((n+1)(n+2))`; the
left leg contributes the same quantity up to the reflection sign
`(-1)ⁿ`, so the two legs double for even `n` and cancel for odd `n`.
The centred moment then follows from the substitution `x = c + u`
together with the binomial theorem.

The absolute value forces an explicit split at `0`: each leg is
computed separately, on its own side, where `|u|` is replaced by `u`
or by `-u` before any polynomial integration happens.

## Main declarations

* `tent` — the tent of half-width `h` centred at `c`.
* `integral_tentProfile_mul_pow` — **the symmetric single-power
  integral**: `∫_{-h}^{h} (1 - |u|/h)·uⁿ du` is
  `2·h^(n+1)/((n+1)(n+2))` for even `n` and `0` for odd `n`.
* `integral_tentProfile_mul_pow_shift` — **the tent moment**: the
  integral of `(1 - |x-c|/h)·x^p` over `[c-h, c+h]`, expanded as a
  sum over `Finset.range (p+1)` of binomial terms carrying the
  even-index filter of the previous theorem.
* `integral_tent_mul_pow` — the same moment written for the truncated
  tent `tent c h`, whose truncation is inactive on `[c-h, c+h]`.
-/

set_option autoImplicit false

open scoped BigOperators
open MeasureTheory

namespace Fabius

/-- The **tent** (hat) function of half-width `h` centred at `c`:
`tent c h x = max (1 - |x - c| / h) 0`. -/
noncomputable def tent (c h x : ℝ) : ℝ := max (1 - |x - c| / h) 0

/-- The two elementary quotients produced by a single tent leg differ
by exactly the reciprocal of `(n+1)(n+2)`. -/
private theorem tent_leg_algebra {h : ℝ} (hh : 0 < h) (n : ℕ) :
    h ^ (n + 1) / ((n : ℝ) + 1)
        - h⁻¹ * (h ^ (n + 1 + 1) / ((n : ℝ) + 2))
      = h ^ (n + 1) / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  have hne : h ≠ 0 := ne_of_gt hh
  have hp : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hq : ((n : ℝ) + 2) ≠ 0 := by positivity
  have hcancel : h⁻¹ * (h ^ (n + 1 + 1) / ((n : ℝ) + 2))
      = h ^ (n + 1) / ((n : ℝ) + 2) := by
    rw [pow_succ h (n + 1), ← mul_div_assoc,
      mul_comm (h ^ (n + 1)) h, ← mul_assoc,
      inv_mul_cancel₀ hne, one_mul]
  have hnum : h ^ (n + 1) * ((n : ℝ) + 2)
      - ((n : ℝ) + 1) * h ^ (n + 1) = h ^ (n + 1) := by ring
  rw [hcancel, div_sub_div _ _ hp hq, hnum]

/-- The tent profile times a monomial is continuous. -/
private theorem continuous_tentProfile_mul_pow (h : ℝ) (n : ℕ) :
    Continuous fun u : ℝ => (1 - |u| / h) * u ^ n :=
  (continuous_const.sub (continuous_abs.div_const h)).mul
    (continuous_pow n)

/-- **The right leg.**  On `[0, h]` the profile is the polynomial
`uⁿ - h⁻¹·u^(n+1)`, whose integral is `h^(n+1)/((n+1)(n+2))`. -/
private theorem integral_tentProfile_right (n : ℕ) {h : ℝ}
    (hh : 0 < h) :
    (∫ u in (0 : ℝ)..h, (1 - |u| / h) * u ^ n)
      = h ^ (n + 1) / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  have heq : ∀ u ∈ Set.uIcc (0 : ℝ) h,
      (1 - |u| / h) * u ^ n = u ^ n - h⁻¹ * u ^ (n + 1) := by
    intro u hu
    rw [Set.uIcc_of_le hh.le] at hu
    rw [abs_of_nonneg hu.1, pow_succ, div_eq_mul_inv]
    ring
  have hint1 : IntervalIntegrable (fun u : ℝ => u ^ n) volume 0 h :=
    (continuous_pow n).intervalIntegrable 0 h
  have hint2 : IntervalIntegrable
      (fun u : ℝ => h⁻¹ * u ^ (n + 1)) volume 0 h :=
    (continuous_const.mul (continuous_pow (n + 1))).intervalIntegrable
      0 h
  have hz1 : (0 : ℝ) ^ (n + 1) = 0 := zero_pow (by omega)
  have hz2 : (0 : ℝ) ^ (n + 1 + 1) = 0 := zero_pow (by omega)
  have hden : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by
    rw [Nat.cast_add, Nat.cast_one]
    ring
  rw [intervalIntegral.integral_congr heq,
    intervalIntegral.integral_sub hint1 hint2,
    integral_pow, intervalIntegral.integral_const_mul, integral_pow,
    hz1, hz2, hden, ← tent_leg_algebra hh n]
  ring

/-- **The left leg.**  On `[-h, 0]` the profile is the polynomial
`uⁿ + h⁻¹·u^(n+1)`; the reflection sign `(-1)ⁿ` is all that
distinguishes it from the right leg. -/
private theorem integral_tentProfile_left (n : ℕ) {h : ℝ}
    (hh : 0 < h) :
    (∫ u in (-h)..(0 : ℝ), (1 - |u| / h) * u ^ n)
      = (-1 : ℝ) ^ n
          * (h ^ (n + 1) / (((n : ℝ) + 1) * ((n : ℝ) + 2))) := by
  have hle : (-h : ℝ) ≤ 0 := by linarith
  have heq : ∀ u ∈ Set.uIcc (-h) (0 : ℝ),
      (1 - |u| / h) * u ^ n = u ^ n + h⁻¹ * u ^ (n + 1) := by
    intro u hu
    rw [Set.uIcc_of_le hle] at hu
    rw [abs_of_nonpos hu.2, pow_succ, div_eq_mul_inv]
    ring
  have hint1 : IntervalIntegrable
      (fun u : ℝ => u ^ n) volume (-h) 0 :=
    (continuous_pow n).intervalIntegrable (-h) 0
  have hint2 : IntervalIntegrable
      (fun u : ℝ => h⁻¹ * u ^ (n + 1)) volume (-h) 0 :=
    (continuous_const.mul (continuous_pow (n + 1))).intervalIntegrable
      (-h) 0
  have hz1 : (0 : ℝ) ^ (n + 1) = 0 := zero_pow (by omega)
  have hz2 : (0 : ℝ) ^ (n + 1 + 1) = 0 := zero_pow (by omega)
  have hden : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by
    rw [Nat.cast_add, Nat.cast_one]
    ring
  rcases Nat.even_or_odd n with hn | hn
  · have hod : Odd (n + 1) := hn.add_one
    have hev : Even (n + 1 + 1) := hod.add_one
    rw [intervalIntegral.integral_congr heq,
      intervalIntegral.integral_add hint1 hint2,
      integral_pow, intervalIntegral.integral_const_mul, integral_pow,
      hz1, hz2, hden, hod.neg_pow h, hev.neg_pow h, hn.neg_one_pow,
      ← tent_leg_algebra hh n]
    ring
  · have hev : Even (n + 1) := hn.add_one
    have hod : Odd (n + 1 + 1) := hev.add_one
    rw [intervalIntegral.integral_congr heq,
      intervalIntegral.integral_add hint1 hint2,
      integral_pow, intervalIntegral.integral_const_mul, integral_pow,
      hz1, hz2, hden, hev.neg_pow h, hod.neg_pow h, hn.neg_one_pow,
      ← tent_leg_algebra hh n]
    ring

/--
**The symmetric single-power tent integral.**  For every `n : ℕ` and
every half-width `h > 0`,

`∫_{-h}^{h} (1 - |u|/h)·uⁿ du = 2·h^(n+1)/((n+1)(n+2))`

when `n` is even, and `0` when `n` is odd.  The two legs of the tent
contribute the same quantity up to the reflection sign `(-1)ⁿ`.
-/
theorem integral_tentProfile_mul_pow (n : ℕ) {h : ℝ} (hh : 0 < h) :
    (∫ u in (-h)..h, (1 - |u| / h) * u ^ n)
      = if Even n then
          2 * h ^ (n + 1) / (((n : ℝ) + 1) * ((n : ℝ) + 2))
        else 0 := by
  have hcont := continuous_tentProfile_mul_pow h n
  have hsplit :
      (∫ u in (-h)..(0 : ℝ), (1 - |u| / h) * u ^ n)
          + ∫ u in (0 : ℝ)..h, (1 - |u| / h) * u ^ n
        = ∫ u in (-h)..h, (1 - |u| / h) * u ^ n :=
    intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable (-h) 0) (hcont.intervalIntegrable 0 h)
  rcases Nat.even_or_odd n with hn | hn
  · rw [if_pos hn, ← hsplit, integral_tentProfile_left n hh,
      integral_tentProfile_right n hh, hn.neg_one_pow]
    ring
  · rw [if_neg (Nat.not_even_iff_odd.mpr hn), ← hsplit,
      integral_tentProfile_left n hh,
      integral_tentProfile_right n hh, hn.neg_one_pow]
    ring

/--
**The tent moment.**  For every centre `c`, every half-width `h > 0`
and every degree `p : ℕ`,

`∫_{c-h}^{c+h} (1 - |x-c|/h)·x^p dx
   = ∑_{k<p+1} C(p,k)·c^(p-k)·[k even]·2·h^(k+1)/((k+1)(k+2))`.

The substitution `x = c + u` recentres the tent at the origin, and the
binomial theorem turns `(c+u)^p` into a finite sum of the symmetric
single-power integrals of `integral_tentProfile_mul_pow`.  Every odd
`k` contributes `0`.
-/
theorem integral_tentProfile_mul_pow_shift (c : ℝ) {h : ℝ}
    (hh : 0 < h) (p : ℕ) :
    (∫ x in (c - h)..(c + h), (1 - |x - c| / h) * x ^ p)
      = ∑ k ∈ Finset.range (p + 1),
          c ^ (p - k) * (p.choose k : ℝ) *
            (if Even k then
              2 * h ^ (k + 1) / (((k : ℝ) + 1) * ((k : ℝ) + 2))
            else 0) := by
  have hcont : ∀ k : ℕ, Continuous fun u : ℝ =>
      c ^ (p - k) * (p.choose k : ℝ) * ((1 - |u| / h) * u ^ k) :=
    fun k => continuous_const.mul (continuous_tentProfile_mul_pow h k)
  have hshift :
      (∫ u in (-h)..h, (1 - |c + u - c| / h) * (c + u) ^ p)
        = ∫ x in (c + -h)..(c + h), (1 - |x - c| / h) * x ^ p :=
    intervalIntegral.integral_comp_add_left
      (fun x : ℝ => (1 - |x - c| / h) * x ^ p) c
  rw [← sub_eq_add_neg] at hshift
  have hexpand : ∀ u ∈ Set.uIcc (-h) h,
      (1 - |c + u - c| / h) * (c + u) ^ p
        = ∑ k ∈ Finset.range (p + 1),
            c ^ (p - k) * (p.choose k : ℝ)
              * ((1 - |u| / h) * u ^ k) := by
    intro u _
    have hcu : c + u - c = u := by ring
    rw [hcu, add_comm c u, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    ring
  have hcgr :
      (∫ u in (-h)..h, (1 - |c + u - c| / h) * (c + u) ^ p)
        = ∫ u in (-h)..h, ∑ k ∈ Finset.range (p + 1),
            c ^ (p - k) * (p.choose k : ℝ)
              * ((1 - |u| / h) * u ^ k) :=
    intervalIntegral.integral_congr hexpand
  have hfs :
      (∫ u in (-h)..h, ∑ k ∈ Finset.range (p + 1),
          c ^ (p - k) * (p.choose k : ℝ)
            * ((1 - |u| / h) * u ^ k))
        = ∑ k ∈ Finset.range (p + 1),
            ∫ u in (-h)..h, c ^ (p - k) * (p.choose k : ℝ)
              * ((1 - |u| / h) * u ^ k) :=
    intervalIntegral.integral_finsetSum
      fun k _ => (hcont k).intervalIntegrable (-h) h
  rw [← hshift, hcgr, hfs]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [intervalIntegral.integral_const_mul,
    integral_tentProfile_mul_pow k hh]

/-- On the support interval `[c-h, c+h]` the truncation in `tent` is
inactive: there `tent c h x = 1 - |x - c| / h`. -/
theorem tent_eq_of_mem_Icc {c h x : ℝ} (hh : 0 < h)
    (hx : x ∈ Set.Icc (c - h) (c + h)) :
    tent c h x = 1 - |x - c| / h := by
  have habs : |x - c| ≤ h :=
    abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hle : |x - c| / h ≤ 1 := (div_le_one hh).mpr habs
  show max (1 - |x - c| / h) 0 = 1 - |x - c| / h
  exact max_eq_left (by linarith)

/--
**The tent moment for the truncated tent.**  Same statement as
`integral_tentProfile_mul_pow_shift`, but written for `tent c h`
itself: the truncation `max · 0` is inactive throughout `[c-h, c+h]`,
so the two integrals agree.
-/
theorem integral_tent_mul_pow (c : ℝ) {h : ℝ} (hh : 0 < h) (p : ℕ) :
    (∫ x in (c - h)..(c + h), tent c h x * x ^ p)
      = ∑ k ∈ Finset.range (p + 1),
          c ^ (p - k) * (p.choose k : ℝ) *
            (if Even k then
              2 * h ^ (k + 1) / (((k : ℝ) + 1) * ((k : ℝ) + 2))
            else 0) := by
  have hcgr : ∀ x ∈ Set.uIcc (c - h) (c + h),
      tent c h x * x ^ p = (1 - |x - c| / h) * x ^ p := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith : c - h ≤ c + h)] at hx
    rw [tent_eq_of_mem_Icc hh hx]
  rw [intervalIntegral.integral_congr hcgr,
    integral_tentProfile_mul_pow_shift c hh p]

end Fabius
