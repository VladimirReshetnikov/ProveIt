import FabiusFunction.KappaOneEnclosure

/-!
# Numerical enclosures for `κ₀`, `κ₂` and `κ∞`

`KappaDictionary` evaluates the decay dictionary at the three
distinguished means,

`κ₀ = κ(1/2) = 3/2 + log₂π`, `κ₂ = κ(√2/2) = 1 + log₂π`,
`κ∞ = κ(√3/2) = 3/2 + log₂(π/√3)`,

and `KappaOneEnclosure` encloses the fourth, `κ₁ = κ(ϱ₁)`, at the
Perron root.  The three closed-form constants had no numerical
enclosure in the corpus, only their exact expressions and the
orderings between them; that is what this module supplies.

The obstruction was never the dictionary but `log π`, which Mathlib
does not carry.  `Fabius.log_pi_bracket` now does, so all three
reduce to rational arithmetic on certified logarithms, and two of
them share a single quantity: `log₂π`.  It is bracketed once
(`logTwo_pi_bracket`) and `κ₀`, `κ₂` are read off by adding `3/2`
and `1`, with no further loss.

Results, all to a width below `2·10⁻⁹`:

`3.1514961287 ≤ κ₀ ≤ 3.1514961300`  (pins `κ₀ = 3.1514961…`)
`2.6514961287 ≤ κ₂ ≤ 2.6514961300`  (pins `κ₂ = 2.6514961…`)
`2.3590148784 ≤ κ∞ ≤ 2.3590148796`  (pins `κ∞ = 2.35901487…`)

Seven decimals for the first two, eight for `κ∞` --- the difference
is where the true values happen to fall relative to a decimal
boundary, not a difference in precision: the three widths are
`1.3·10⁻⁹`, `1.3·10⁻⁹` and `1.2·10⁻⁹`.

The logarithms are taken in their **tightest** Mathlib form,
`Real.log_two_near_10` and `Real.log_three_near_10` (half-width
`10⁻¹⁰`, exact rational centres), rather than the `_d9` corollaries
used in `KappaOneEnclosure` (half-widths `2.5·10⁻¹⁰` and
`1.5·10⁻¹⁰`).  That choice roughly halves the final widths and costs
nothing.  What now dominates is `log π` itself, whose `5·10⁻¹⁰`
width is inherited from the `_d9` form of `log 3` used to prove it;
re-deriving it from `log_three_near_10` would shrink these
enclosures by a further factor of about two but would not pin
another decimal of `κ₀` or `κ₂`, for the boundary reason above.

* `Fabius.div_bracket` — bracketing a quotient of positives, the
  only piece of interval arithmetic used;
* `Fabius.log_two_lower`, `Fabius.log_two_upper`,
  `Fabius.log_three_lower`, `Fabius.log_three_upper` — the two
  Mathlib constants as two-sided bounds with exact rational
  endpoints;
* `Fabius.logTwo_pi_bracket` — **`log₂π` to seven decimals**;
* `Fabius.kappa_zero_bracket`, `Fabius.kappa_two_bracket`,
  `Fabius.kappa_inf_bracket` — the three enclosures;
* `Fabius.kappa_inf_lt_kappa_two_numeric` — a numerical
  confirmation of the ordering `KappaDictionary` proves exactly.
-/

set_option autoImplicit false

open Real

namespace Fabius

/-! ## Interval arithmetic -/

/-- **Bracketing a quotient.**  If `a` and `b` are trapped in
`[a₀,a₁]` and `[b₀,b₁]` with `a₀ > 0` and `b₀ > 0`, then `a / b` is
trapped in `[a₀/b₁, a₁/b₀]`: the quotient is largest when the
numerator is largest and the denominator smallest.

Positivity of `a₀` is used only to know the numerator is
nonnegative, which is what lets the two multiplications be
monotone. -/
theorem div_bracket {a b a₀ a₁ b₀ b₁ : ℝ} (ha₀ : 0 < a₀)
    (hb₀ : 0 < b₀) (ha : a₀ ≤ a) (ha' : a ≤ a₁) (hb : b₀ ≤ b)
    (hb' : b ≤ b₁) :
    a₀ / b₁ ≤ a / b ∧ a / b ≤ a₁ / b₀ := by
  have hbpos : (0 : ℝ) < b := lt_of_lt_of_le hb₀ hb
  have hb₁ : (0 : ℝ) < b₁ := lt_of_lt_of_le hbpos hb'
  have hapos : (0 : ℝ) ≤ a := le_trans ha₀.le ha
  have ha₁ : (0 : ℝ) ≤ a₁ := le_trans hapos ha'
  constructor
  · rw [div_le_div_iff₀ hb₁ hbpos]
    have h1 : a₀ * b ≤ a * b :=
      mul_le_mul_of_nonneg_right ha hbpos.le
    have h2 : a * b ≤ a * b₁ := mul_le_mul_of_nonneg_left hb' hapos
    linarith
  · rw [div_le_div_iff₀ hbpos hb₀]
    have h1 : a * b₀ ≤ a₁ * b₀ :=
      mul_le_mul_of_nonneg_right ha' hb₀.le
    have h2 : a₁ * b₀ ≤ a₁ * b := mul_le_mul_of_nonneg_left hb ha₁
    linarith

/-! ## The two Mathlib logarithms, two-sidedly

`Real.log_two_near_10` and `Real.log_three_near_10` are absolute-value
statements about an exact rational centre.  Splitting them keeps that
exact centre, which is tighter than the `_d9` decimal corollaries. -/

/-- Lower bound for `log 2`, exact rational endpoint. -/
theorem log_two_lower :
    (287209 / 414355 - 1 / 10 ^ 10 : ℝ) ≤ Real.log 2 := by
  have h := (abs_sub_le_iff.mp Real.log_two_near_10).2
  linarith

/-- Upper bound for `log 2`, exact rational endpoint. -/
theorem log_two_upper :
    Real.log 2 ≤ 287209 / 414355 + 1 / 10 ^ 10 := by
  have h := (abs_sub_le_iff.mp Real.log_two_near_10).1
  linarith

/-- Lower bound for `log 3`, exact rational endpoint. -/
theorem log_three_lower :
    (109861228867 / 100000000000 - 1 / 10 ^ 10 : ℝ) ≤ Real.log 3 := by
  have h := (abs_sub_le_iff.mp Real.log_three_near_10).2
  linarith

/-- Upper bound for `log 3`, exact rational endpoint. -/
theorem log_three_upper :
    Real.log 3 ≤ 109861228867 / 100000000000 + 1 / 10 ^ 10 := by
  have h := (abs_sub_le_iff.mp Real.log_three_near_10).1
  linarith

/-! ## `log₂π` -/

/-- **`log₂π` to seven decimals**, `log₂π = 1.6514961…`.

This is the quantity `κ₀` and `κ₂` differ from `3/2` and `1` by, so
bracketing it once serves both.  The numerator is
`Fabius.log_pi_bracket`; the denominator is `log 2` at its exact
rational centre. -/
theorem logTwo_pi_bracket :
    (1.6514961287 : ℝ) ≤ Real.log π / Real.log 2 ∧
      Real.log π / Real.log 2 ≤ 1.6514961300 := by
  have h := div_bracket (a₀ := (1.1447298855 : ℝ))
    (a₁ := (1.1447298860 : ℝ))
    (b₀ := (287209 / 414355 - 1 / 10 ^ 10 : ℝ))
    (b₁ := (287209 / 414355 + 1 / 10 ^ 10 : ℝ))
    (by norm_num) (by norm_num) log_pi_gt.le log_pi_lt.le
    log_two_lower log_two_upper
  exact ⟨le_trans (by norm_num) h.1, le_trans h.2 (by norm_num)⟩

/-! ## The three enclosures -/

/-- **`κ₀ = 3.1514961…`**, the `L¹`-trivial exponent at the mean
`Λ = 1/2`.  Width `1.3·10⁻⁹`. -/
theorem kappa_zero_bracket :
    (3.1514961287 : ℝ) ≤ kappaOf (1 / 2) ∧
      kappaOf (1 / 2) ≤ 3.1514961300 := by
  rw [kappaOf_half]
  obtain ⟨h1, h2⟩ := logTwo_pi_bracket
  exact ⟨by linarith, by linarith⟩

/-- **`κ₂ = 2.6514961…`**, the root-mean-square exponent at
`Λ = √2/2`.  Width `1.3·10⁻⁹`.  It is exactly `κ₀ - 1/2`
(`Fabius.kappa_zero_sub_kappa_two`), which the two enclosures
visibly respect. -/
theorem kappa_two_bracket :
    (2.6514961287 : ℝ) ≤ kappaOf (Real.sqrt 2 / 2) ∧
      kappaOf (Real.sqrt 2 / 2) ≤ 2.6514961300 := by
  rw [kappaOf_sqrt_two]
  obtain ⟨h1, h2⟩ := logTwo_pi_bracket
  exact ⟨by linarith, by linarith⟩

/-- **`κ∞ = 2.35901487…`**, the sharp Gelfond exponent at
`Λ = √3/2`, and the extremal member of the family.  Width
`1.2·10⁻⁹`, eight decimals.

Here `log 3` enters as well, through
`log(π/√3) = log π - (log 3)/2`. -/
theorem kappa_inf_bracket :
    (2.3590148784 : ℝ) ≤ kappaInf ∧ kappaInf ≤ 2.3590148796 := by
  have hps : Real.log (π / Real.sqrt 3)
      = Real.log π - Real.log 3 / 2 := by
    rw [Real.log_div Real.pi_ne_zero (by positivity),
      Real.log_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  have hlo : (0.59542374111 : ℝ) ≤ Real.log π - Real.log 3 / 2 := by
    have h1 := log_pi_gt
    have h2 := log_three_upper
    linarith
  have hhi : Real.log π - Real.log 3 / 2 ≤ 0.59542374172 := by
    have h1 := log_pi_lt
    have h2 := log_three_lower
    linarith
  have h := div_bracket (a₀ := (0.59542374111 : ℝ))
    (a₁ := (0.59542374172 : ℝ))
    (b₀ := (287209 / 414355 - 1 / 10 ^ 10 : ℝ))
    (b₁ := (287209 / 414355 + 1 / 10 ^ 10 : ℝ))
    (by norm_num) (by norm_num) hlo hhi log_two_lower log_two_upper
  rw [kappaInf, hps]
  refine ⟨?_, ?_⟩
  · have := h.1
    have hb : (0.8590148784 : ℝ) ≤
        (Real.log π - Real.log 3 / 2) / Real.log 2 :=
      le_trans (by norm_num) this
    linarith
  · have := h.2
    have hb : (Real.log π - Real.log 3 / 2) / Real.log 2
        ≤ 0.8590148796 := le_trans this (by norm_num)
    linarith

/-- The ordering `κ∞ < κ₂`, which `Fabius.kappaInf_lt_kappa_two`
proves exactly, confirmed numerically by the two enclosures: the
upper end of `κ∞` falls below the lower end of `κ₂`. -/
theorem kappa_inf_lt_kappa_two_numeric :
    kappaInf < kappaOf (Real.sqrt 2 / 2) :=
  lt_of_le_of_lt kappa_inf_bracket.2
    (lt_of_lt_of_le (by norm_num) kappa_two_bracket.1)

end Fabius
