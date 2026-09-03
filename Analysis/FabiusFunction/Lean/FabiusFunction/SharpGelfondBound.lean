import FabiusFunction.GelfondLogisticBound

/-!
# The sharp Gelfond bound: `‖Pₙ‖∞ ≤ (√3/2)ⁿ⁻¹`

The calibrated Gelfond bound of `GelfondLogisticBound` carries the
constant `√(5/3)`.  Documents 5 and 6 of the second-wave Fourier-decay
corpus (audited in the second-wave comparative audit) remove it: the
dyadic sine product satisfies the *sharp* bound
`∏_{j<n} |sin (π 2ʲ t)| ≤ (√3/2)^{n-1}`, which together with the exact
value `(√3/2)ⁿ` at `t = 1/3` brackets the sup-norm between consecutive
powers of the Gelfond constant.

The mechanism is a **two-step subaction**: the weighted inequality
`(2/3)·log|sin θ| + (1/3)·log|sin 2θ| ≤ log(√3/2)`, which in
multiplicative form reads `|sin θ|²·|sin 2θ| ≤ (√3/2)³` and reduces to
the quartic `u³(1-u) ≤ 27/256` for `u = sin²θ`.  Multiplying it along
the orbit and regrouping cubes gives one factor of `√3/2` per step
after the first.

This file formalizes the mechanism in more generality than the text:

* `cube_mul_one_sub_le` — `u³(1-u) ≤ 27/256` for **every** real `u`
  (not only `u ∈ [0,1]`), by an exact sum-of-squares identity.
* `prod_pow_three_eq` — the cube of a running product regroups as
  `first · lastⁿ⁻¹²… ` — precisely
  `(∏_{j≤n} s j)³ = s 0 · s n ² · ∏_{j<n} (s j ² · s (j+1))`;
  pure commutative algebra.
* `prod_le_pow_of_sq_mul_succ_le` — the **two-step product
  principle**: any sequence with values in `[0,1]` whose adjacent
  pairs satisfy `s j ² · s (j+1) ≤ c³` has
  `∏_{j≤n} s j ≤ cⁿ`.  This applies to every weighted doubling system
  whose maximizing orbit is a two-cycle, not only to sines.
* `sin_sq_sq_mul_sin_sq_two_mul_le`, `abs_sin_sq_mul_abs_sin_two_mul_le`
  — the sharp two-step inequality for sines, squared and modulus forms.
* `prod_sin_sq_two_pow_le_sharp`, `abs_prod_sin_two_pow_le_sharp` —
  the sharp Gelfond bounds `∏_{j≤n} sin(π 2ʲ t)² ≤ (3/4)ⁿ` and
  `∏_{j≤n} |sin(π 2ʲ t)| ≤ (√3/2)ⁿ` (with `n+1` factors: the
  `‖Pₙ‖∞ ≤ λ^{n-1}` of the audit, stated without natural subtraction).
* `abs_sin_two_pow_third`, `abs_prod_sin_two_pow_third` — attainment:
  at `t = 1/3` every factor is exactly `√3/2`, so
  `(√3/2)ⁿ ≤ ‖Pₙ‖∞ ≤ (√3/2)ⁿ⁻¹`.
-/

set_option autoImplicit false

open Finset Real

namespace Fabius

/-- The quartic inequality behind the sharp two-step subaction: for
**every** real `u`, `u³(1-u) ≤ 27/256`, by the exact sum-of-squares
identity `27/256 - u³(1-u) = ((u-3/4)(u+1/4))² + (u-3/4)²/8`. -/
theorem cube_mul_one_sub_le (u : ℝ) : u ^ 3 * (1 - u) ≤ 27 / 256 := by
  nlinarith [sq_nonneg ((u - 3 / 4) * (u + 1 / 4)), sq_nonneg (u - 3 / 4)]

/-- Regrouping the cube of a running product into two-step blocks:
`(∏_{j≤n} s j)³ = s 0 · (s n)² · ∏_{j<n} ((s j)² · s (j+1))`. -/
theorem prod_pow_three_eq (s : ℕ → ℝ) (n : ℕ) :
    (∏ j ∈ range (n + 1), s j) ^ 3 =
      s 0 * s n ^ 2 * ∏ j ∈ range n, (s j ^ 2 * s (j + 1)) := by
  induction n with
  | zero =>
      rw [Finset.prod_range_one, Finset.prod_range_zero, mul_one]
      ring
  | succ n ihn =>
      rw [prod_range_succ, mul_pow, ihn, prod_range_succ]
      ring

/-- **Two-step product principle, boundary form**: only the two
boundary factors need a bound — if `0 ≤ s j`, `s 0 · (s n)² ≤ 1` and
every adjacent pair satisfies `(s j)² · s (j+1) ≤ c³`, then
`∏_{j≤n} s j ≤ cⁿ`.  The interior factors may exceed `1`. -/
theorem prod_le_pow_of_sq_mul_succ_le_of_boundary {s : ℕ → ℝ} {c : ℝ}
    (h0 : ∀ j, 0 ≤ s j) (hc : 0 ≤ c)
    (hpair : ∀ j, s j ^ 2 * s (j + 1) ≤ c ^ 3) (n : ℕ)
    (hfront : s 0 * s n ^ 2 ≤ 1) :
    ∏ j ∈ range (n + 1), s j ≤ c ^ n := by
  refine le_of_pow_le_pow_left₀ (by norm_num : (3:ℕ) ≠ 0) (pow_nonneg hc n) ?_
  rw [prod_pow_three_eq]
  have hblocks : ∏ j ∈ range n, (s j ^ 2 * s (j + 1)) ≤
      ∏ _j ∈ range n, c ^ 3 :=
    Finset.prod_le_prod (fun j _ => mul_nonneg (sq_nonneg _) (h0 _))
      (fun j _ => hpair j)
  rw [Finset.prod_const, Finset.card_range] at hblocks
  have hb0 : 0 ≤ ∏ j ∈ range n, (s j ^ 2 * s (j + 1)) :=
    Finset.prod_nonneg fun j _ => mul_nonneg (sq_nonneg _) (h0 _)
  calc s 0 * s n ^ 2 * ∏ j ∈ range n, (s j ^ 2 * s (j + 1))
      ≤ 1 * (c ^ 3) ^ n := mul_le_mul hfront hblocks hb0 (by norm_num)
    _ = (c ^ n) ^ 3 := by ring

/-- **Two-step product principle**: if `0 ≤ s j ≤ 1` and every adjacent
pair satisfies `(s j)² · s (j+1) ≤ c³`, then `∏_{j≤n} s j ≤ cⁿ`.
This is the abstract form of the sharp Gelfond bound: a two-cycle
subaction yields one factor of `c` per step after the first.  It is the
boundary form with `s 0 · (s n)² ≤ 1` read off from `s ≤ 1`. -/
theorem prod_le_pow_of_sq_mul_succ_le {s : ℕ → ℝ} {c : ℝ}
    (h0 : ∀ j, 0 ≤ s j) (h1 : ∀ j, s j ≤ 1) (hc : 0 ≤ c)
    (hpair : ∀ j, s j ^ 2 * s (j + 1) ≤ c ^ 3) (n : ℕ) :
    ∏ j ∈ range (n + 1), s j ≤ c ^ n := by
  refine prod_le_pow_of_sq_mul_succ_le_of_boundary h0 hc hpair n ?_
  have hsn : s n ^ 2 ≤ 1 := by
    have hn0 := h0 n
    have hn1 := h1 n
    nlinarith
  calc s 0 * s n ^ 2 ≤ 1 * 1 :=
        mul_le_mul (h1 0) hsn (sq_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- The sharp two-step inequality, squared form:
`(sin²θ)² · sin²(2θ) ≤ (3/4)³`. -/
theorem sin_sq_sq_mul_sin_sq_two_mul_le (θ : ℝ) :
    (Real.sin θ ^ 2) ^ 2 * Real.sin (2 * θ) ^ 2 ≤ (3 / 4 : ℝ) ^ 3 := by
  have h := cube_mul_one_sub_le (Real.sin θ ^ 2)
  rw [sin_sq_two_mul]
  nlinarith [h]

/-- The sharp two-step inequality, modulus form:
`|sin θ|² · |sin 2θ| ≤ (√3/2)³`. -/
theorem abs_sin_sq_mul_abs_sin_two_mul_le (θ : ℝ) :
    |Real.sin θ| ^ 2 * |Real.sin (2 * θ)| ≤ (Real.sqrt 3 / 2) ^ 3 := by
  refine le_of_pow_le_pow_left₀ (by norm_num : (2:ℕ) ≠ 0) (by positivity) ?_
  have hsq : (|Real.sin θ| ^ 2 * |Real.sin (2 * θ)|) ^ 2 =
      (Real.sin θ ^ 2) ^ 2 * Real.sin (2 * θ) ^ 2 := by
    rw [mul_pow, sq_abs, sq_abs]
  have hrhs : ((Real.sqrt 3 / 2) ^ 3) ^ 2 = (3 / 4 : ℝ) ^ 3 := by
    rw [← pow_mul, show 3 * 2 = 2 * 3 from rfl, pow_mul, div_pow,
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    norm_num
  rw [hsq, hrhs]
  exact sin_sq_sq_mul_sin_sq_two_mul_le θ

/-- **The sharp Gelfond bound, squared form**: with `n+1` factors,
`∏_{j≤n} sin (π 2ʲ t)² ≤ (3/4)ⁿ`. -/
theorem prod_sin_sq_two_pow_le_sharp (t : ℝ) (n : ℕ) :
    ∏ j ∈ range (n + 1), Real.sin (π * 2 ^ j * t) ^ 2 ≤ (3 / 4 : ℝ) ^ n := by
  refine prod_le_pow_of_sq_mul_succ_le (fun j => sq_nonneg _)
    (fun j => Real.sin_sq_le_one _) (by norm_num) (fun j => ?_) n
  have harg : π * 2 ^ (j + 1) * t = 2 * (π * 2 ^ j * t) := by ring
  rw [harg]
  exact sin_sq_sq_mul_sin_sq_two_mul_le _

/-- **The sharp Gelfond bound** (Documents 5/6 of the second wave): with
`n+1` factors, `∏_{j≤n} |sin (π 2ʲ t)| ≤ (√3/2)ⁿ` — the audit's
`‖Pₙ‖∞ ≤ (√3/2)^{n-1}`, improving `abs_prod_sin_two_pow_le` by the
factor `√(5/3)·(√3/2) = √(5/4) > 1`. -/
theorem abs_prod_sin_two_pow_le_sharp (t : ℝ) (n : ℕ) :
    ∏ j ∈ range (n + 1), |Real.sin (π * 2 ^ j * t)| ≤
      (Real.sqrt 3 / 2) ^ n := by
  refine prod_le_pow_of_sq_mul_succ_le (fun j => abs_nonneg _)
    (fun j => abs_sin_le_one _) (by positivity) (fun j => ?_) n
  have harg : π * 2 ^ (j + 1) * t = 2 * (π * 2 ^ j * t) := by ring
  rw [harg]
  exact abs_sin_sq_mul_abs_sin_two_mul_le _

/-- On the extremal two-cycle every sine factor is exactly `√3/2`:
`|sin (π 2ʲ / 3)| = √3/2`. -/
theorem abs_sin_two_pow_third (j : ℕ) :
    |Real.sin (π * 2 ^ j * (1 / 3 : ℝ))| = Real.sqrt 3 / 2 := by
  have h34 : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    norm_num
  calc |Real.sin (π * 2 ^ j * (1 / 3 : ℝ))|
      = Real.sqrt (Real.sin (π * 2 ^ j * (1 / 3 : ℝ)) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ = Real.sqrt ((Real.sqrt 3 / 2) ^ 2) := by
        rw [sin_sq_two_pow_third, h34]
    _ = Real.sqrt 3 / 2 := Real.sqrt_sq (by positivity)

/-- **Attainment of the sharp rate**: at `t = 1/3`,
`∏_{j<n} |sin (π 2ʲ / 3)| = (√3/2)ⁿ` exactly.  Together with
`abs_prod_sin_two_pow_le_sharp` this brackets the sup-norm of the
dyadic sine product between `(√3/2)ⁿ` and `(√3/2)ⁿ⁻¹`. -/
theorem abs_prod_sin_two_pow_third (n : ℕ) :
    ∏ j ∈ range n, |Real.sin (π * 2 ^ j * (1 / 3 : ℝ))| =
      (Real.sqrt 3 / 2) ^ n := by
  rw [Finset.prod_congr rfl fun j _ => abs_sin_two_pow_third j,
    Finset.prod_const, Finset.card_range]

end Fabius
