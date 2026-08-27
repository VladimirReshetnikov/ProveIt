import FabiusFunction.LacunaryRieszIntegral

/-!
# The Gelfond bound via a logistic-orbit telescope

The sharp exponential rate of the sup-norm of dyadic sine products —
the constant behind the extremal exponent `κ∞` of the Fourier-decay
audit — is governed by a single algebraic inequality for the full
logistic map `v ↦ 4v(1-v)`.  This file formalizes that mechanism in a
form more general than the sine products themselves: the bound holds
along **every** orbit of the logistic map that starts in `[0,1]`
(equivalently, by `logistic_init_le_one`, along every orbit that stays
nonnegative), and the sine products enter only because squared sines
at doubling angles form such orbits.

* `logistic_nonneg_and_le_one` — the unit interval is **invariant**
  under `v ↦ 4v(1-v)`; the upper half is `1 - 4v(1-v) = (2v-1)² ≥ 0`.
* `logistic_orbit_nonneg_and_le_one` — hence an orbit whose *starting
  point* lies in `[0,1]` stays in `[0,1]` forever.
* `logistic_prod_le_of_init` — along any orbit
  `u (j+1) = 4·u j·(1 - u j)` with `0 ≤ u 0 ≤ 1` — a hypothesis on
  `u 0` **only** — the running product satisfies
  `∏_{j<n} u j ≤ (5/3)·(3/4)ⁿ`.  The proof telescopes the potential
  `V v = 1 + 2v/3` through the exact identity
  `3·V v - 4v·V (4v(1-v)) = (2v+1)(4v-3)²/3`, which holds for every
  real `v`; its right-hand side is `≥ 0` because the orbit keeps
  `2v + 1 > 0`
  (Document 2's subaction, audited in the comparative audit).
* `logistic_init_le_one`, `logistic_prod_le_of_nonneg` — for a logistic
  orbit, `∀ j, 0 ≤ u j` already forces `u 0 ≤ 1`, so the bound holds
  under nonnegativity alone.
* `logistic_prod_le` — the original blanket-hypothesis form
  (`∀ j, 0 ≤ u j` and `∀ j, u j ≤ 1`), now a corollary: both range
  hypotheses are redundant away from `j = 0`.
* `logistic_prod_eq_of_init_three_quarters` — the rate `(3/4)ⁿ` is
  **exact** already at the abstract level: `3/4` is the interior fixed
  point of the logistic map, and the constant orbit it generates has
  running product exactly `(3/4)ⁿ`.
* `prod_sin_sq_two_pow_mul_le` — the **potential-carrying** form of
  the Gelfond bound, i.e. what the telescope literally proves:
  `(∏_{j<n} sin (π 2ʲ t)²)·(1 + 2 sin (π 2ⁿ t)²/3)
     ≤ (3/4)ⁿ·(1 + 2 sin (π t)²/3)` for every real `t`.
* `prod_sin_sq_two_pow_le` — the **Gelfond bound**
  `∏_{j<n} sin (π 2ʲ t)² ≤ (5/3)·(3/4)ⁿ` for every real `t`; the
  calibrated consequence of the previous item.
* `sin_sq_two_pow_eq_three_quarters`,
  `prod_sin_sq_two_pow_eq_of_sin_sq_eq` — **sharpness in general
  position**: *every* `t` seeding the fixed point, i.e. with
  `sin (π t)² = 3/4`, has all its doubling iterates at `3/4` and hence
  `∏_{j<n} sin (π 2ʲ t)² = (3/4)ⁿ`.  This covers `t = 1/3`, `t = 2/3`
  and all their integer translates at once.
* `prod_sin_sq_two_pow_third` — **sharpness**: at `t = 1/3` every
  factor equals `3/4`, so the product is exactly `(3/4)ⁿ`; the binary
  cycle `1/3 ↔ 2/3` realizes the extremal rate.
* `prod_abs_sq` — the elementary bridge
  `(∏ i ∈ s, |f i|)² = ∏ i ∈ s, (f i)²` used to pass between the
  squared and the modulus forms of the bound.
* `abs_prod_sin_two_pow_le` — the unsquared form
  `∏_{j<n} |sin (π 2ʲ t)| ≤ √(5/3)·(√3/2)ⁿ`.
* `le_mul_integral_prod_abs_sin_two_pow` — combining the Gelfond bound
  with the exact `L²` identity of `LacunaryRieszIntegral`:
  `(1/2)ⁿ ≤ √(5/3)·(√3/2)ⁿ · ∫ t in 0..1, ∏_{j<n} |sin (π 2ʲ t)|`,
  i.e. the mean of the sine product is at least `√(3/5)·3^{-n/2}`.
  This is the elementary lower bracket `ϱ₁ ≥ 3^{-1/2} > 1/2` used by
  the audit to prove that the transfer-operator eigenmeasure is
  singular (impossibility of the exact Cesàro limit).
-/

set_option autoImplicit false

open Finset intervalIntegral Real

namespace Fabius

/-- The subaction step: for `v ≥ 0`,
`4v·(1 + 2·(4v(1-v))/3) ≤ 3·(1 + 2v/3)`, by the exact identity
`3·V v - 4v·V (4v(1-v)) = (2v+1)(4v-3)²/3`, whose right-hand side is
nonnegative because `2v + 1 > 0`.  No upper bound on `v` is used. -/
theorem logistic_subaction_step (v : ℝ) (h0 : 0 ≤ v) :
    4 * v * (1 + 2 * (4 * v * (1 - v)) / 3) ≤ 3 * (1 + 2 * v / 3) := by
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 * v + 1) (sq_nonneg (4 * v - 3)),
    sq_nonneg (4 * v - 3)]

/-- Telescoped form: along a logistic orbit, the weighted running
product is controlled at every step. -/
theorem logistic_prod_mul_le (u : ℕ → ℝ) (h0 : ∀ j, 0 ≤ u j)
    (hrec : ∀ j, u (j + 1) = 4 * u j * (1 - u j)) :
    ∀ n : ℕ, (∏ j ∈ range n, u j) * (1 + 2 * u n / 3) ≤
      (3 / 4 : ℝ) ^ n * (1 + 2 * u 0 / 3) := by
  intro n
  induction n with
  | zero => simp
  | succ n ihn =>
      have hstep : u n * (1 + 2 * u (n + 1) / 3) ≤
          (3 / 4) * (1 + 2 * u n / 3) := by
        have h := logistic_subaction_step (u n) (h0 n)
        rw [hrec n]
        linarith
      have hprod0 : 0 ≤ ∏ j ∈ range n, u j :=
        Finset.prod_nonneg fun j _ => h0 j
      calc (∏ j ∈ range (n + 1), u j) * (1 + 2 * u (n + 1) / 3)
          = (∏ j ∈ range n, u j) * (u n * (1 + 2 * u (n + 1) / 3)) := by
            rw [Finset.prod_range_succ]; ring
        _ ≤ (∏ j ∈ range n, u j) * ((3 / 4) * (1 + 2 * u n / 3)) :=
            mul_le_mul_of_nonneg_left hstep hprod0
        _ = (3 / 4) * ((∏ j ∈ range n, u j) * (1 + 2 * u n / 3)) := by ring
        _ ≤ (3 / 4) * ((3 / 4 : ℝ) ^ n * (1 + 2 * u 0 / 3)) := by
            have h34 : (0:ℝ) ≤ 3 / 4 := by norm_num
            exact mul_le_mul_of_nonneg_left ihn h34
        _ = (3 / 4 : ℝ) ^ (n + 1) * (1 + 2 * u 0 / 3) := by ring

/-- **Invariance of the unit interval** under the full logistic map:
if `0 ≤ v ≤ 1` then `0 ≤ 4v(1-v) ≤ 1`.  The upper bound is the exact
identity `1 - 4v(1-v) = (2v-1)²`. -/
theorem logistic_nonneg_and_le_one (v : ℝ) (h0 : 0 ≤ v) (h1 : v ≤ 1) :
    0 ≤ 4 * v * (1 - v) ∧ 4 * v * (1 - v) ≤ 1 := by
  constructor
  · nlinarith [mul_nonneg h0 (by linarith : (0:ℝ) ≤ 1 - v)]
  · nlinarith [sq_nonneg (2 * v - 1)]

/-- A logistic orbit started in `[0,1]` never leaves it: from
`0 ≤ u 0 ≤ 1` alone, `0 ≤ u j ≤ 1` for **every** `j`. -/
theorem logistic_orbit_nonneg_and_le_one (u : ℕ → ℝ) (h0 : 0 ≤ u 0)
    (h1 : u 0 ≤ 1) (hrec : ∀ j, u (j + 1) = 4 * u j * (1 - u j)) :
    ∀ j, 0 ≤ u j ∧ u j ≤ 1 := by
  intro j
  induction j with
  | zero => exact ⟨h0, h1⟩
  | succ j ihj =>
      rw [hrec j]
      exact logistic_nonneg_and_le_one (u j) ihj.1 ihj.2

/-- **Logistic-orbit product bound, initial-value form**: along any
orbit of the full logistic map `v ↦ 4v(1-v)` whose *starting point*
lies in `[0,1]`, `∏_{j<n} u j ≤ (5/3)·(3/4)ⁿ`.

Only `u 0` is constrained: the range hypotheses at `j ≥ 1` are
supplied by `logistic_orbit_nonneg_and_le_one`, and the constant `5/3`
comes from `1 + 2·u 0/3 ≤ 5/3`, i.e. from `u 0 ≤ 1` alone. -/
theorem logistic_prod_le_of_init (u : ℕ → ℝ) (h0 : 0 ≤ u 0) (h1 : u 0 ≤ 1)
    (hrec : ∀ j, u (j + 1) = 4 * u j * (1 - u j)) (n : ℕ) :
    ∏ j ∈ range n, u j ≤ 5 / 3 * (3 / 4 : ℝ) ^ n := by
  have hnonneg : ∀ j, 0 ≤ u j := fun j =>
    (logistic_orbit_nonneg_and_le_one u h0 h1 hrec j).1
  have hprod0 : 0 ≤ ∏ j ∈ range n, u j :=
    Finset.prod_nonneg fun j _ => hnonneg j
  have h := logistic_prod_mul_le u hnonneg hrec n
  have hup : (∏ j ∈ range n, u j) ≤
      (∏ j ∈ range n, u j) * (1 + 2 * u n / 3) := by
    nlinarith [mul_nonneg hprod0 (hnonneg n)]
  have hV0 : 1 + 2 * u 0 / 3 ≤ 5 / 3 := by linarith
  have hpow : (0:ℝ) ≤ (3 / 4 : ℝ) ^ n := by positivity
  have hkey : (3 / 4 : ℝ) ^ n * (1 + 2 * u 0 / 3) ≤
      (3 / 4 : ℝ) ^ n * (5 / 3) := mul_le_mul_of_nonneg_left hV0 hpow
  linarith

/-- For a logistic orbit, nonnegativity of the iterates already pins
the starting point down: `∀ j, 0 ≤ u j` forces `u 0 ≤ 1`, because
`u 1 = 4·u 0·(1 - u 0)` would otherwise be negative. -/
theorem logistic_init_le_one (u : ℕ → ℝ) (h0 : ∀ j, 0 ≤ u j)
    (hrec : ∀ j, u (j + 1) = 4 * u j * (1 - u j)) : u 0 ≤ 1 := by
  by_contra hcon
  push Not at hcon
  have hstep : 0 ≤ 4 * u 0 * (1 - u 0) := by
    rw [← hrec 0]
    exact h0 _
  nlinarith [sq_nonneg (u 0 - 1)]

/-- **Logistic-orbit product bound, nonnegativity form**: for an orbit
of `v ↦ 4v(1-v)`, nonnegativity of every iterate is by itself enough
for `∏_{j<n} u j ≤ (5/3)·(3/4)ⁿ`; no upper bound need be assumed
anywhere.  Along an orbit this hypothesis is *equivalent* to the
`0 ≤ u 0 ≤ 1` of `logistic_prod_le_of_init`, by `logistic_init_le_one`
in one direction and `logistic_orbit_nonneg_and_le_one` in the
other. -/
theorem logistic_prod_le_of_nonneg (u : ℕ → ℝ) (h0 : ∀ j, 0 ≤ u j)
    (hrec : ∀ j, u (j + 1) = 4 * u j * (1 - u j)) (n : ℕ) :
    ∏ j ∈ range n, u j ≤ 5 / 3 * (3 / 4 : ℝ) ^ n :=
  logistic_prod_le_of_init u (h0 0) (logistic_init_le_one u h0 hrec) hrec n

/-- **Logistic-orbit product bound**: along any orbit of the full
logistic map `v ↦ 4v(1-v)` in `[0,1]`,
`∏_{j<n} u j ≤ (5/3)·(3/4)ⁿ`.  Corollary of `logistic_prod_le_of_init`,
which uses the two range hypotheses only at `j = 0`. -/
theorem logistic_prod_le (u : ℕ → ℝ) (h0 : ∀ j, 0 ≤ u j) (h1 : ∀ j, u j ≤ 1)
    (hrec : ∀ j, u (j + 1) = 4 * u j * (1 - u j)) (n : ℕ) :
    ∏ j ∈ range n, u j ≤ 5 / 3 * (3 / 4 : ℝ) ^ n :=
  logistic_prod_le_of_init u (h0 0) (h1 0) hrec n

/-- **The rate `(3/4)ⁿ` of `logistic_prod_le_of_init` is exact.**  The
value `3/4` is the interior fixed point of `v ↦ 4v(1-v)`, so an orbit
started there is constant and its running product is exactly `(3/4)ⁿ`.
Consequently no geometric rate smaller than `(3/4)ⁿ` holds along all
logistic orbits, whatever the constant in front. -/
theorem logistic_prod_eq_of_init_three_quarters (u : ℕ → ℝ)
    (h0 : u 0 = 3 / 4) (hrec : ∀ j, u (j + 1) = 4 * u j * (1 - u j))
    (n : ℕ) : ∏ j ∈ range n, u j = (3 / 4 : ℝ) ^ n := by
  have hfix : ∀ j, u j = 3 / 4 := by
    intro j
    induction j with
    | zero => exact h0
    | succ j ihj =>
        rw [hrec j, ihj]
        norm_num
  rw [Finset.prod_congr rfl fun j _ => hfix j, Finset.prod_const,
    Finset.card_range]

/-- Squared sines at doubling angles form a logistic orbit:
`sin (2x)² = 4·sin x²·(1 - sin x²)`. -/
theorem sin_sq_two_mul (x : ℝ) :
    Real.sin (2 * x) ^ 2 = 4 * Real.sin x ^ 2 * (1 - Real.sin x ^ 2) := by
  rw [Real.sin_two_mul]
  have h := Real.sin_sq_add_cos_sq x
  nlinarith [h]

/-- **The Gelfond bound with its telescoping factor retained.**  What
the logistic telescope literally proves at `u j = sin (π 2ʲ t)²` — the
potential `V v = 1 + 2v/3` evaluated at both ends of the orbit — is

`(∏_{j<n} sin (π 2ʲ t)²)·(1 + 2 sin (π 2ⁿ t)²/3)
   ≤ (3/4)ⁿ·(1 + 2 sin (π t)²/3)`,

valid for every real `t`.  Discarding the left factor (which is `≥ 1`)
and bounding the right one by `5/3` gives `prod_sin_sq_two_pow_le`;
keeping both is strictly stronger — it is sharper by the factor
`(1 + 2 sin (π 2ⁿ t)²/3)` at the far end and by
`(1 + 2 sin (π t)²/3)/(5/3)` at the seed, and both gains are genuine
unless the orbit sits at the fixed point. -/
theorem prod_sin_sq_two_pow_mul_le (t : ℝ) (n : ℕ) :
    (∏ j ∈ range n, Real.sin (π * 2 ^ j * t) ^ 2) *
        (1 + 2 * Real.sin (π * 2 ^ n * t) ^ 2 / 3) ≤
      (3 / 4 : ℝ) ^ n * (1 + 2 * Real.sin (π * t) ^ 2 / 3) := by
  have hrec : ∀ j : ℕ, Real.sin (π * 2 ^ (j + 1) * t) ^ 2 =
      4 * Real.sin (π * 2 ^ j * t) ^ 2 *
        (1 - Real.sin (π * 2 ^ j * t) ^ 2) := by
    intro j
    have harg : π * 2 ^ (j + 1) * t = 2 * (π * 2 ^ j * t) := by ring
    rw [harg, sin_sq_two_mul]
  have h := logistic_prod_mul_le (fun j => Real.sin (π * 2 ^ j * t) ^ 2)
    (fun j => sq_nonneg _) hrec n
  have hzero : Real.sin (π * 2 ^ (0 : ℕ) * t) ^ 2 =
      Real.sin (π * t) ^ 2 := by
    norm_num
  simpa only [hzero] using h

/-- **The Gelfond bound**, squared form: for every real `t`,
`∏_{j<n} sin (π 2ʲ t)² ≤ (5/3)·(3/4)ⁿ`.  This is the sup-norm rate of
the dyadic sine product; it forces the extremal power `κ∞` of the
Fourier-decay spectrum.  No hypothesis on `t` is needed: the squared
sine orbit starts in `[0,1]` automatically.  The stronger,
potential-carrying statement that the telescope actually delivers is
`prod_sin_sq_two_pow_mul_le`. -/
theorem prod_sin_sq_two_pow_le (t : ℝ) (n : ℕ) :
    ∏ j ∈ range n, Real.sin (π * 2 ^ j * t) ^ 2 ≤ 5 / 3 * (3 / 4 : ℝ) ^ n := by
  refine logistic_prod_le (fun j => Real.sin (π * 2 ^ j * t) ^ 2)
    (fun j => sq_nonneg _) (fun j => Real.sin_sq_le_one _) (fun j => ?_) n
  have harg : π * 2 ^ (j + 1) * t = 2 * (π * 2 ^ j * t) := by ring
  rw [harg, sin_sq_two_mul]

/-- **Sharpness in general position**: if the *initial* squared sine
already sits at the logistic fixed point, `sin (π t)² = 3/4`, then the
whole doubling orbit stays there: `sin (π 2ʲ t)² = 3/4` for every `j`.
The hypothesis holds exactly for `t ∈ ±1/3 + ℤ`, so this covers
`t = 1/3`, `t = 2/3` and all their integer translates at once. -/
theorem sin_sq_two_pow_eq_three_quarters {t : ℝ}
    (ht : Real.sin (π * t) ^ 2 = 3 / 4) (j : ℕ) :
    Real.sin (π * 2 ^ j * t) ^ 2 = 3 / 4 := by
  induction j with
  | zero =>
      have harg : π * 2 ^ 0 * t = π * t := by ring
      rw [harg]
      exact ht
  | succ j ihj =>
      have harg : π * 2 ^ (j + 1) * t = 2 * (π * 2 ^ j * t) := by ring
      rw [harg, sin_sq_two_mul, ihj]
      norm_num

/-- The extremal orbit is attained on the nose: at every seed with
`sin (π t)² = 3/4` the dyadic squared-sine product equals `(3/4)ⁿ`,
so the Gelfond rate cannot be improved. -/
theorem prod_sin_sq_two_pow_eq_of_sin_sq_eq {t : ℝ}
    (ht : Real.sin (π * t) ^ 2 = 3 / 4) (n : ℕ) :
    ∏ j ∈ range n, Real.sin (π * 2 ^ j * t) ^ 2 = (3 / 4 : ℝ) ^ n := by
  have hfac : ∀ j : ℕ, Real.sin (π * 2 ^ j * t) ^ 2 = 3 / 4 :=
    fun j => sin_sq_two_pow_eq_three_quarters ht j
  rw [Finset.prod_congr rfl fun j _ => hfac j, Finset.prod_const,
    Finset.card_range]

/-- The seed of the extremal two-cycle: `sin (π/3)² = 3/4`. -/
theorem sin_sq_pi_third : Real.sin (π * (1 / 3 : ℝ)) ^ 2 = 3 / 4 := by
  have harg : π * (1 / 3 : ℝ) = π / 3 := by ring
  rw [harg, Real.sin_pi_div_three]
  rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  norm_num

/-- **Sharpness of the Gelfond bound**: every factor of the dyadic sine
product at `t = 1/3` equals `3/4`. -/
theorem sin_sq_two_pow_third (j : ℕ) :
    Real.sin (π * 2 ^ j * (1 / 3 : ℝ)) ^ 2 = 3 / 4 :=
  sin_sq_two_pow_eq_three_quarters sin_sq_pi_third j

/-- At `t = 1/3` the dyadic sine product attains the Gelfond rate
exactly: `∏_{j<n} sin (π 2ʲ/3)² = (3/4)ⁿ`. -/
theorem prod_sin_sq_two_pow_third (n : ℕ) :
    ∏ j ∈ range n, Real.sin (π * 2 ^ j * (1 / 3 : ℝ)) ^ 2 = (3 / 4 : ℝ) ^ n := by
  rw [Finset.prod_congr rfl fun j _ => sin_sq_two_pow_third j,
    Finset.prod_const, Finset.card_range]

/-- Squaring commutes with a finite product of absolute values:
`(∏ i ∈ s, |f i|)² = ∏ i ∈ s, (f i)²`.  Elementary, but it is the
bridge used twice below to move between the squared Gelfond bound and
its modulus form. -/
theorem prod_abs_sq {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∏ i ∈ s, |f i|) ^ 2 = ∏ i ∈ s, f i ^ 2 := by
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun i _ => sq_abs _

/-- The Gelfond bound, unsquared form:
`∏_{j<n} |sin (π 2ʲ t)| ≤ √(5/3)·(√3/2)ⁿ`. -/
theorem abs_prod_sin_two_pow_le (t : ℝ) (n : ℕ) :
    ∏ j ∈ range n, |Real.sin (π * 2 ^ j * t)| ≤
      Real.sqrt (5 / 3) * (Real.sqrt 3 / 2) ^ n := by
  set A : ℝ := ∏ j ∈ range n, |Real.sin (π * 2 ^ j * t)| with hA
  have hA0 : 0 ≤ A := Finset.prod_nonneg fun j _ => abs_nonneg _
  have hAsq : A ^ 2 = ∏ j ∈ range n, Real.sin (π * 2 ^ j * t) ^ 2 := by
    rw [hA]
    exact prod_abs_sq (range n) fun j => Real.sin (π * 2 ^ j * t)
  set B : ℝ := Real.sqrt (5 / 3) * (Real.sqrt 3 / 2) ^ n with hB
  have hB0 : 0 ≤ B := by positivity
  have hBsq : B ^ 2 = 5 / 3 * (3 / 4 : ℝ) ^ n := by
    rw [hB, mul_pow, ← pow_mul, mul_comm n 2, pow_mul, div_pow,
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5 / 3),
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    norm_num
  have hle : A ^ 2 ≤ B ^ 2 := by
    rw [hAsq, hBsq]
    exact prod_sin_sq_two_pow_le t n
  calc A = Real.sqrt (A ^ 2) := (Real.sqrt_sq hA0).symm
    _ ≤ Real.sqrt (B ^ 2) := Real.sqrt_le_sqrt hle
    _ = B := Real.sqrt_sq hB0

/-- **Lower bracket for the mean of the dyadic sine product.**
Combining the exact `L²` identity `∫ ∏ sin² = (1/2)ⁿ` with the Gelfond
sup bound gives
`(1/2)ⁿ ≤ √(5/3)·(√3/2)ⁿ · ∫ t in 0..1, ∏_{j<n} |sin (π 2ʲ t)|`.
Equivalently, `I₁(n) ≥ √(3/5)·3^{-n/2}`: the per-level `L¹` rate of
the sine product is at least `3^{-1/2} > 1/2`.  This is the fully
elementary input that makes the transfer-operator eigenmeasure of the
decay audit singular. -/
theorem le_mul_integral_prod_abs_sin_two_pow (n : ℕ) :
    (1 / 2 : ℝ) ^ n ≤ (Real.sqrt (5 / 3) * (Real.sqrt 3 / 2) ^ n) *
      ∫ t in (0:ℝ)..1, ∏ j ∈ range n, |Real.sin (π * 2 ^ j * t)| := by
  set B : ℝ := Real.sqrt (5 / 3) * (Real.sqrt 3 / 2) ^ n with hB
  have hB0 : 0 ≤ B := by positivity
  have hQcont : Continuous fun t : ℝ =>
      ∏ j ∈ range n, |Real.sin (π * 2 ^ j * t)| := by
    refine continuous_finsetProd _ fun j _ => ?_
    fun_prop
  have hQsqcont : Continuous fun t : ℝ =>
      ∏ j ∈ range n, Real.sin (π * 2 ^ j * t) ^ 2 := by
    refine continuous_finsetProd _ fun j _ => ?_
    fun_prop
  have hpoint : ∀ t ∈ Set.Icc (0:ℝ) 1,
      ∏ j ∈ range n, Real.sin (π * 2 ^ j * t) ^ 2 ≤
        B * ∏ j ∈ range n, |Real.sin (π * 2 ^ j * t)| := by
    intro t _
    have hQ0 : 0 ≤ ∏ j ∈ range n, |Real.sin (π * 2 ^ j * t)| :=
      Finset.prod_nonneg fun j _ => abs_nonneg _
    have hQle : ∏ j ∈ range n, |Real.sin (π * 2 ^ j * t)| ≤ B :=
      abs_prod_sin_two_pow_le t n
    have hsq : ∏ j ∈ range n, Real.sin (π * 2 ^ j * t) ^ 2 =
        (∏ j ∈ range n, |Real.sin (π * 2 ^ j * t)|) ^ 2 :=
      (prod_abs_sq (range n) fun j => Real.sin (π * 2 ^ j * t)).symm
    rw [hsq, sq]
    exact mul_le_mul_of_nonneg_right hQle hQ0
  have hgcont : Continuous fun t : ℝ =>
      B * ∏ j ∈ range n, |Real.sin (π * 2 ^ j * t)| := hQcont.const_mul B
  have hmono := intervalIntegral.integral_mono_on
    (μ := MeasureTheory.volume) (by norm_num : (0:ℝ) ≤ 1)
    (hQsqcont.intervalIntegrable 0 1)
    (hgcont.intervalIntegrable 0 1) hpoint
  rw [intervalIntegral.integral_const_mul] at hmono
  calc (1 / 2 : ℝ) ^ n
      = ∫ t in (0:ℝ)..1, ∏ j ∈ range n, Real.sin (π * 2 ^ j * t) ^ 2 :=
        (integral_prod_sin_sq_two_pow n).symm
    _ ≤ B * ∫ t in (0:ℝ)..1, ∏ j ∈ range n, |Real.sin (π * 2 ^ j * t)| := hmono

end Fabius
