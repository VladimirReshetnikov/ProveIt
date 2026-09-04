import FabiusFunction.SharpFlatness
import FabiusFunction.StirlingAsymptotics

/-!
# A two-term endpoint upper bound from the flatness family

The transseries volume's `plt:prop:mot-fabius-endpoint`.  The corpus
carries the sharp flatness family
(`fabiusReal_le_two_pow_div_factorial_mul_pow`)

`F(x) ≤ 2^C(n+1,2)/n! · xⁿ`   valid whenever `2ⁿ x ≤ 1`,

one inequality for each `n`.  Optimizing the free index turns the family
into a *quadratic-in-log* decay law: writing `ℓ = log(1/x)` and
`a = log 2`, the choice `n = ⌊ℓ/a⌋` gives, for every `0 < x ≤ 1/4`,

`log F(x) ≤ -ℓ²/(2a) - ℓ log ℓ / a + (1/2 + 3/a)·ℓ`.

Both the quadratic term and the `ℓ log ℓ` correction are of the true
order; only the linear term is wasteful, and it is explicit.

The two halves of the optimization are isolated as reusable estimates.
The quadratic part is exact bookkeeping: with `m = ℓ/a` and `θ = m - n`
the flatness exponent contributes `-a(m² - m + θ - θ²)/2`, and `θ - θ²≥0`
on `[0,1)` is the whole of it.  The factorial part is Stirling's crude
half `log n! ≥ n log n - n` (taken from the corpus's sharp Stirling
bounds) together with the rounding estimate
`m log m - n log n ≤ log m + 1`, itself just `log t ≤ t - 1` applied to
`t = m/n`.

* `fabiusReal_le_exp_endpoint` — **the bound**, in exponential form, so
  that it needs no positivity hypothesis.
* `log_fabiusReal_le_endpoint` — the same in the logarithmic form the
  volume states.

The volume's companion `plt:cor:mot-fabius-inverse`
(`log(1/G(y)) ≤ √(2B log 2) + O(1)`, `B = log(1/y)`) is *not* reproved
here: the corpus already has the strictly sharper two-sided law
`log_fabiusInv_sub_fabiusInverseLogAsymptoticMain_isBigO`, whose main
term `fabiusInverseLogAsymptoticMain` is
`-√(2 log2 · B) + (log B)/2 - 1 - log(log 2)/2` with error
`O(log B/√B)`.  What this module adds over that asymptotic statement is
effectivity: an inequality with explicit constants, valid from `x = 1/4`
down, rather than a statement about a limit.
-/

set_option autoImplicit false

namespace Fabius

/-- `log n! ≥ n log n - n`, the crude half of Stirling. -/
private theorem log_factorial_lower {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * Real.log n - n ≤ Real.log (n.factorial : ℝ) := by
  have h := (log_factorial_sub_stirlingMain_bounds n hn).1
  have hlogn : (0 : ℝ) ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hpi : (0 : ℝ) ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.two_le_pi])
  linarith

/-- Rounding down costs at most `log m + 1` in `m log m`. -/
private theorem mul_log_sub_mul_log_le {m : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hnm : (n : ℝ) ≤ m) (hmn : m < (n : ℝ) + 1) :
    m * Real.log m - (n : ℝ) * Real.log n ≤ Real.log m + 1 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le hnpos hnm
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg (by linarith)
  have hdiv : Real.log (m / (n : ℝ)) = Real.log m - Real.log n :=
    Real.log_div hmpos.ne' hnpos.ne'
  have hkey : Real.log (m / (n : ℝ)) ≤ m / (n : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h1 : (n : ℝ) * (Real.log m - Real.log n) ≤ m - (n : ℝ) := by
    have h2 := mul_le_mul_of_nonneg_left hkey hnpos.le
    rw [hdiv] at h2
    calc (n : ℝ) * (Real.log m - Real.log n)
        ≤ (n : ℝ) * (m / (n : ℝ) - 1) := h2
      _ = m - (n : ℝ) := by field_simp
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - (m - (n : ℝ))) hlogm]

/-- The quadratic part of the endpoint estimate. -/
private theorem quadratic_part {a m l : ℝ} (ha : 0 < a) (hl : l = a * m)
    {n : ℝ} (h1 : n ≤ m) (h2 : m < n + 1) :
    a * ((n + 1) * n / 2) - n * l ≤ -l ^ 2 / (2 * a) + l / 2 := by
  have hsq : l ^ 2 / (2 * a) = a * m ^ 2 / 2 := by
    rw [hl]; field_simp
  rw [neg_div, hsq, hl]
  nlinarith [sq_nonneg (m - n), mul_nonneg ha.le
    (mul_nonneg (by linarith : (0 : ℝ) ≤ m - n)
      (by linarith : (0 : ℝ) ≤ 1 - (m - n)))]

/-- **A two-term endpoint upper bound** (`plt:prop:mot-fabius-endpoint`). -/
theorem fabiusReal_le_exp_endpoint (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 4) :
    fabiusReal F x ≤
      Real.exp (-Real.log (1 / x) ^ 2 / (2 * Real.log 2) -
        Real.log (1 / x) * Real.log (Real.log (1 / x)) / Real.log 2 +
        (1 / 2 + 3 / Real.log 2) * Real.log (1 / x)) := by
  have ha : 0 < Real.log 2 := Real.log_pos one_lt_two
  have ha1 : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
      (by norm_num : (2:ℝ) ≠ 1)
    linarith
  set a := Real.log 2 with ha_def
  set l := Real.log (1 / x) with hl_def
  have hlx : l = -Real.log x := by rw [hl_def, one_div, Real.log_inv]
  have hlog4 : Real.log (1 / 4 : ℝ) = -(2 * a) := by
    rw [one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hl2a : 2 * a ≤ l := by
    have := Real.log_le_log hx0 hx
    rw [hlog4] at this
    rw [hlx]
    linarith
  have hlpos : 0 < l := by nlinarith
  set m := l / a with hm_def
  have hlam : l = a * m := by rw [hm_def]; field_simp
  have hm2 : 2 ≤ m := by
    rw [hm_def, le_div_iff₀ ha]
    linarith
  set n := ⌊m⌋₊ with hn_def
  have hn2 : 2 ≤ n := Nat.le_floor (by exact_mod_cast hm2)
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn2
  have hnm : (n : ℝ) ≤ m := Nat.floor_le (by linarith)
  have hmn : m < (n : ℝ) + 1 := Nat.lt_floor_add_one m
  have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  -- the dyadic scale hypothesis
  have hna : (n : ℝ) * a ≤ l := by
    rw [hlam]
    nlinarith
  have hscale : (2 : ℝ) ^ n * x ≤ 1 := by
    have hxinv : (0 : ℝ) < x⁻¹ := by positivity
    have hlogx : Real.log x⁻¹ = l := by rw [hlx, Real.log_inv]
    have hpow : Real.log ((2 : ℝ) ^ n) = (n : ℝ) * a := by
      rw [Real.log_pow]
    have hle : (2 : ℝ) ^ n ≤ x⁻¹ := by
      rw [← Real.log_le_log_iff (by positivity) hxinv, hpow, hlogx]
      exact hna
    calc (2 : ℝ) ^ n * x ≤ x⁻¹ * x :=
          mul_le_mul_of_nonneg_right hle hx0.le
      _ = 1 := inv_mul_cancel₀ hx0.ne'
  have hflat := fabiusReal_le_two_pow_div_factorial_mul_pow F hF n hx0.le hscale
  -- bound the flatness right-hand side by the exponential
  set B : ℝ := 2 ^ (n + 1).choose 2 / (n.factorial : ℝ) * x ^ n with hB_def
  have hBpos : 0 < B := by
    rw [hB_def]
    have : (0 : ℝ) < (n.factorial : ℝ) := by positivity
    positivity
  have hchoose : (((n + 1).choose 2 : ℕ) : ℝ) = ((n : ℝ) + 1) * (n : ℝ) / 2 := by
    rw [Nat.cast_choose_two]
    push_cast
    ring
  have hlogB : Real.log B =
      a * (((n : ℝ) + 1) * (n : ℝ) / 2) - Real.log (n.factorial : ℝ) -
        (n : ℝ) * l := by
    have hfacpos : (0 : ℝ) < (n.factorial : ℝ) := by positivity
    rw [hB_def, Real.log_mul (by positivity) (by positivity),
      Real.log_div (by positivity) hfacpos.ne', Real.log_pow, Real.log_pow,
      hchoose, hlx]
    ring
  -- the two halves
  have hA1 : a * (((n : ℝ) + 1) * (n : ℝ) / 2) - (n : ℝ) * l ≤
      -l ^ 2 / (2 * a) + l / 2 :=
    quadratic_part ha hlam hnm hmn
  have hlogm : Real.log m ≤ m - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hlogmnn : 0 ≤ Real.log m := Real.log_nonneg (by linarith)
  have hmlog : m * Real.log m - (n : ℝ) * Real.log n ≤ Real.log m + 1 :=
    mul_log_sub_mul_log_le hn1 hnm hmn
  have hfac := log_factorial_lower hn1
  have hloga : Real.log a < 0 := Real.log_neg ha ha1
  have hmlogm : Real.log m = Real.log l - Real.log a := by
    rw [hm_def, Real.log_div hlpos.ne' ha.ne']
  have hA2 : -Real.log (n.factorial : ℝ) ≤ -(l * Real.log l / a) + 3 * l / a := by
    have hstep : -Real.log (n.factorial : ℝ) ≤ -(m * Real.log m) + Real.log m + 1 + m := by
      linarith
    have hmm : m * Real.log m = (l / a) * (Real.log l - Real.log a) := by
      rw [← hmlogm, hm_def]
    have hkey : -(m * Real.log m) ≤ -(l * Real.log l / a) := by
      rw [hmm]
      have : (l / a) * (Real.log l - Real.log a) =
          l * Real.log l / a - (l / a) * Real.log a := by ring
      rw [this]
      have hpos : 0 < l / a := by positivity
      have hprod : 0 ≤ (l / a) * (-Real.log a) :=
        mul_nonneg hpos.le (neg_nonneg.mpr hloga.le)
      nlinarith [hprod]
    have hmval : m = l / a := hm_def
    have hla : (0 : ℝ) ≤ l / a := by positivity
    have hthree : 2 * (l / a) ≤ 3 * l / a := by
      rw [show (3 : ℝ) * l / a = 3 * (l / a) by ring]
      linarith
    calc -Real.log (n.factorial : ℝ)
        ≤ -(m * Real.log m) + Real.log m + 1 + m := hstep
      _ ≤ -(l * Real.log l / a) + (m - 1) + 1 + m := by linarith
      _ = -(l * Real.log l / a) + 2 * m := by ring
      _ = -(l * Real.log l / a) + 2 * (l / a) := by rw [hmval]
      _ ≤ -(l * Real.log l / a) + 3 * l / a := by linarith
  have hfinal : Real.log B ≤
      -l ^ 2 / (2 * a) - l * Real.log l / a + (1 / 2 + 3 / a) * l := by
    rw [hlogB]
    have hexpand : (1 / 2 + 3 / a) * l = l / 2 + 3 * l / a := by
      field_simp
    rw [hexpand]
    linarith
  calc fabiusReal F x ≤ B := hflat
    _ = Real.exp (Real.log B) := (Real.exp_log hBpos).symm
    _ ≤ _ := Real.exp_le_exp.mpr hfinal

/-- **The logarithmic form.**  Since `F` is strictly positive at every
positive argument, the exponential bound may be read as a bound on
`log F(x)`, which is the shape `plt:eq:mot-fabius-endpoint` is stated in:

`log F(x) ≤ -ℓ²/(2 log 2) - ℓ log ℓ / log 2 + (1/2 + 3/log 2)·ℓ`,
`ℓ = log(1/x)`. -/
theorem log_fabiusReal_le_endpoint (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 4) :
    Real.log (fabiusReal F x) ≤
      -Real.log (1 / x) ^ 2 / (2 * Real.log 2) -
        Real.log (1 / x) * Real.log (Real.log (1 / x)) / Real.log 2 +
        (1 / 2 + 3 / Real.log 2) * Real.log (1 / x) := by
  have hpos : 0 < fabiusReal F x := fabius_pos_of_pos F hF hx0
  have hle := fabiusReal_le_exp_endpoint F hF hx0 hx
  calc Real.log (fabiusReal F x)
      ≤ Real.log (Real.exp _) := Real.log_le_log hpos hle
    _ = _ := Real.log_exp _

end Fabius
