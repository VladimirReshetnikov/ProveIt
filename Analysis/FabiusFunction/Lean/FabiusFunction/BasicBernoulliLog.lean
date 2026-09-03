import FabiusFunction.SincZetaSeries
import FabiusFunction.EvenZetaValues
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The basic Bernoulli logarithmic expansion

`lem:basic-bernoulli-log` of the `q`-Pochhammer / `q`-binomial monograph,
equation (19.1):

`log ((1 - exp (-x)) / x) = -x/2 + ∑_{r ≥ 1} B_{2r} x^{2r} / (2r · (2r)!)`,

the series converging for `|x| < 2π`.  The Bernoulli convention fixed just
above the lemma is `x / (exp x - 1) = ∑_r B_r x^r / r!`, i.e. `B_1 = -1/2`,
which is exactly Mathlib's `bernoulli` (not `bernoulli'`).

The source proves this by differentiating the left side, quoting the analytic
Bernoulli generating function for `1/(e^x - 1) - 1/x` and integrating term by
term.  None of that route is used here: Mathlib carries only the *formal*
power-series identity `bernoulliPowerSeries_mul_exp_sub_one`, with no analytic
statement about `x / (exp x - 1)`.  Instead the corpus's own Euler–zeta
expansion of the sinc (`complexSinc_pi_mul_eq_cexp`) is rotated by `i`.
Substituting `x := i·u/(2π)` does three things at once: `‖x‖ < 1` becomes
`‖u‖ < 2π`, the sinc becomes `(1 - exp (-u))/u` up to the factor
`exp (-u/2)`, and `ζ(2r)` becomes `B_{2r}` through `evenZeta_eq_bernoulli`.
The arithmetic is exact, no inequality is lost:

`(-1)^{r+1} ζ(2r) / (r (2π)^{2r}) = B_{2r} / (2r (2r)!)`.

## What is covered

* `bernoulliLogCoeff` — the rational coefficient
  `B_{2(r+1)} / (2(r+1)·(2(r+1))!)` of `x^{2(r+1)}`; the sum over `r : ℕ`
  realizes the source's `∑_{r ≥ 1}`.  `bernoulliLogCoeff_zero` is the
  source's own check `B_2 / (2·2!) = 1/24`.
* `one_sub_cexp_neg` — the full identity over `ℂ` on the whole open disk
  `‖u‖ < 2π`, in branch-free multiplicative form
  `1 - exp (-u) = u · exp (-u/2 + ∑' r, c_r · u^{2(r+1)})`, which is valid at
  `u = 0` as well; `one_sub_cexp_neg_div` is its quotient form for `u ≠ 0`.
* `summable_bernoulliLogTerm` and `summable_bernoulliLogTerm_real` — the
  source's "the series converges for `|x| < 2π`" — together with the explicit
  geometric majorant `norm_bernoulliLogTerm_le`,
  `‖c_r u^{2(r+1)}‖ ≤ (π²/6)·(‖u‖/(2π))^{2(r+1)}`.
* `log_one_sub_rexp_neg_div` — equation (19.1) literally, for real `x` with
  `x ≠ 0` and `|x| < 2π`.  The real logarithm is honest there because
  `(1 - e^{-x})/x > 0` for every real `x ≠ 0`; that positivity is delivered
  here in the stronger form `(1 - e^{-x})/x = exp (…)`.

## What is *not* covered

* Nothing of `thm:gaussian-bernoulli` or `cor:gaussian-first-asymptotic`.
* No claim that `2π` is the *exact* radius of convergence.  The source's
  remark "the nearest nonzero singularities are at `±2πi`" is not formalized;
  only convergence on `|x| < 2π` is proved, which is exactly what the
  downstream range `|t| < 2π/n` needs.
* No complex-logarithm form.  For complex `u` the identity is stated
  exponentially, since `Complex.log` of a product is not additive; the source
  writes a bare `log`.  The branch-free form is strictly stronger.

## More general than the source

The source's framing "as `x → 0`" becomes an exact identity on the full
complex disk `‖u‖ < 2π`, and the multiplicative form holds unconditionally at
`u = 0`, where the source's quotient `(1 - e^{-x})/x` has a removable
singularity that the source never mentions.  No further axis of generality is
available: `Complex.exp`, `π` and the radius `2π` pin the statement to `ℂ`
(with its `ℝ` corollary); there is no commutative-ring or general
complete-normed-field version.
-/

set_option autoImplicit false

open Complex Real
open scoped Nat

namespace Fabius

/-! ## The rational coefficients of (19.1) -/

/-- The coefficient of `x^{2(r+1)}` in the basic logarithmic expansion
(19.1): `B_{2(r+1)} / (2(r+1) · (2(r+1))!)`.  Indexing by `r : ℕ` realizes
the source's sum `∑_{r ≥ 1}` over positive `r`. -/
def bernoulliLogCoeff (r : ℕ) : ℚ :=
  bernoulli (2 * (r + 1)) / (2 * ((r : ℚ) + 1) * ((2 * (r + 1))! : ℚ))

/-- The source's own sanity check: `B_2 / (2 · 2!) = 1/24`. -/
theorem bernoulliLogCoeff_zero : bernoulliLogCoeff 0 = 1 / 24 := by
  norm_num [bernoulliLogCoeff, bernoulli_two]

/-- The real form of the coefficient, with every cast pushed to the leaves. -/
theorem ofReal_bernoulliLogCoeff (r : ℕ) :
    (bernoulliLogCoeff r : ℝ) =
      (bernoulli (2 * (r + 1)) : ℝ) /
        (2 * ((r : ℝ) + 1) * ((2 * (r + 1))! : ℝ)) := by
  simp only [bernoulliLogCoeff]
  push_cast
  ring

/-- A cancellation identity in a field, with every ingredient an atom so that
`ring` can see the two sides as the same monomial. -/
private theorem coeff_algebra_aux {S T P B F R : ℝ} (h2R : (2 : ℝ) * R ≠ 0) :
    S * T * P * B / F = S * (B / (2 * R * F)) * (R * (2 * T * P)) := by
  have h1 : S * (B / (2 * R * F)) * (R * (2 * T * P)) =
      S * T * P * B / F * ((2 * R) / (2 * R)) := by
    ring
  rw [h1, div_self h2R, mul_one]

/-- **The exact conversion `ζ(2r) ↦ B_{2r}`.**  For every `r : ℕ`,

`ζ(2(r+1)) = (-1)^r · c_r · ((r+1) · (2π)^{2(r+1)})`,

where `c_r = bernoulliLogCoeff r`.  Equivalently
`c_r = (-1)^r ζ(2(r+1)) / ((r+1)(2π)^{2(r+1)})`; this is the identity that
turns the corpus's Euler–zeta expansion of the sinc into (19.1). -/
theorem evenZeta_eq_bernoulliLogCoeff (r : ℕ) :
    evenZeta (r + 1) =
      (-1 : ℝ) ^ r * (bernoulliLogCoeff r : ℝ) *
        (((r : ℝ) + 1) * (2 * π) ^ (2 * (r + 1))) := by
  have hrnn : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg (α := ℝ) r
  have h2R : (2 : ℝ) * ((r : ℝ) + 1) ≠ 0 := by
    intro hc
    linarith
  have hsign : (-1 : ℝ) ^ (r + 1 + 1) = (-1 : ℝ) ^ r := by
    rw [show r + 1 + 1 = r + 2 by omega, pow_add]
    norm_num
  have hpow2 : (2 : ℝ) ^ (2 * (r + 1)) = 2 * (2 : ℝ) ^ (2 * r + 1) := by
    rw [show 2 * (r + 1) = 2 * r + 1 + 1 by omega, pow_succ]
    ring
  have hpow : ((2 : ℝ) * π) ^ (2 * (r + 1)) =
      2 * (2 : ℝ) ^ (2 * r + 1) * π ^ (2 * (r + 1)) := by
    rw [mul_pow, hpow2]
  have h := evenZeta_eq_bernoulli (k := r + 1) (by omega)
  rw [show 2 * (r + 1) - 1 = 2 * r + 1 by omega, hsign] at h
  rw [h, ofReal_bernoulliLogCoeff, hpow]
  exact coeff_algebra_aux h2R

/-! ## The rotated Euler–zeta series -/

/-- Rotating by `i` and rescaling by `2π` turns the sinc's disk `‖x‖ < 1`
into the disk `‖u‖ < 2π` of (19.1). -/
private theorem norm_rot (u : ℂ) :
    ‖Complex.I * u / (2 * (π : ℂ))‖ = ‖u‖ / (2 * π) := by
  have hpipos : (0 : ℝ) < 2 * π := by
    have := Real.pi_pos
    linarith
  have h2pi : ((2 * π : ℝ) : ℂ) = 2 * (π : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [norm_div, norm_mul, Complex.norm_I, one_mul, ← h2pi, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hpipos]

/-- The rotation sends the sinc's argument `π · x` to `i·u/2`. -/
private theorem pi_mul_rot (u : ℂ) :
    (π : ℂ) * (Complex.I * u / (2 * (π : ℂ))) = Complex.I * u / 2 := by
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  rw [← mul_div_assoc, div_eq_div_iff (mul_ne_zero h2 hpi) h2]
  ring

/-- A cancellation identity in a field with all ingredients atomic; `A`, `B`
carry the two signs `(-1)^r`, `(-1)^{r+1}`. -/
private theorem cancel_algebra_aux {A B c R P U : ℂ} (hR : R ≠ 0) (hP : P ≠ 0)
    (hAB : A * B = -1) :
    -(A * c * (R * P) * (B * (U / P)) / R) = c * U := by
  have h1 : A * c * (R * P) * (B * (U / P)) / R =
      A * B * c * U * ((R / R) * (P / P)) := by
    ring
  rw [h1, div_self hR, div_self hP, hAB]
  ring

/-- **The pointwise heart of the rotation.**  Every term of the Euler–zeta
series of the sinc, evaluated at the rotated variable `i·u/(2π)` and negated,
is the corresponding Bernoulli term of (19.1).  Purely algebraic: no
summability is used. -/
theorem neg_sincZetaTerm_eq_bernoulliLogTerm (u : ℂ) (r : ℕ) :
    -((evenZeta (r + 1) : ℂ) *
        (Complex.I * u / (2 * (π : ℂ))) ^ (2 * (r + 1)) / ((r : ℂ) + 1)) =
      (bernoulliLogCoeff r : ℂ) * u ^ (2 * (r + 1)) := by
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have hP : (2 * (π : ℂ)) ^ (2 * (r + 1)) ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero h2 hpi)
  have hR : ((r : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero r
  have hsq : (Complex.I * u / (2 * (π : ℂ))) ^ 2 =
      -(u ^ 2 / (2 * (π : ℂ)) ^ 2) := by
    rw [div_pow, mul_pow, Complex.I_sq, neg_one_mul, neg_div]
  have hpow : (Complex.I * u / (2 * (π : ℂ))) ^ (2 * (r + 1)) =
      (-1 : ℂ) ^ (r + 1) *
        (u ^ (2 * (r + 1)) / (2 * (π : ℂ)) ^ (2 * (r + 1))) := by
    rw [pow_mul, hsq, neg_pow, div_pow, ← pow_mul, ← pow_mul]
  have hzC : ((evenZeta (r + 1) : ℝ) : ℂ) =
      (-1 : ℂ) ^ r * (bernoulliLogCoeff r : ℂ) *
        (((r : ℂ) + 1) * (2 * (π : ℂ)) ^ (2 * (r + 1))) := by
    rw [evenZeta_eq_bernoulliLogCoeff r]
    push_cast
    ring
  have hsign : (-1 : ℂ) ^ r * (-1 : ℂ) ^ (r + 1) = -1 := by
    rw [← pow_add, show r + (r + 1) = 2 * r + 1 by omega, pow_succ, pow_mul]
    norm_num
  rw [hzC, hpow]
  exact cancel_algebra_aux hR hP hsign

/-! ## Clearing the removable denominator -/

/-- `u · sinc (i·u/2) = e^{u/2} - e^{-u/2}`, unconditionally — including at
`u = 0`, where both sides vanish.  This is what lets the main identity be
stated with no case split. -/
theorem mul_complexSinc_I_div_two (u : ℂ) :
    u * complexSinc (Complex.I * u / 2) =
      Complex.exp (u / 2) - Complex.exp (-u / 2) := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  · have h2 : (2 : ℂ) ≠ 0 := by norm_num
    have hz : Complex.I * u / 2 ≠ 0 :=
      div_ne_zero (mul_ne_zero Complex.I_ne_zero hu) h2
    have h1 : -(Complex.I * u / 2) * Complex.I = u / 2 := by
      linear_combination (-(u / 2)) * Complex.I_sq
    have h2' : Complex.I * u / 2 * Complex.I = -u / 2 := by
      linear_combination (u / 2) * Complex.I_sq
    have hsin : Complex.sin (Complex.I * u / 2) =
        (Complex.exp (u / 2) - Complex.exp (-u / 2)) * Complex.I / 2 := by
      show (Complex.exp (-(Complex.I * u / 2) * Complex.I) -
          Complex.exp (Complex.I * u / 2 * Complex.I)) * Complex.I / 2 =
        (Complex.exp (u / 2) - Complex.exp (-u / 2)) * Complex.I / 2
      rw [h1, h2']
    have hux : u * ((Complex.exp (u / 2) - Complex.exp (-u / 2)) *
          Complex.I / 2) =
        (Complex.exp (u / 2) - Complex.exp (-u / 2)) * (Complex.I * u / 2) := by
      ring
    rw [complexSinc, if_neg hz, hsin, ← mul_div_assoc, hux, mul_div_assoc,
      div_self hz, mul_one]

/-- The elementary exponential bookkeeping behind (19.1): once
`e^{u/2} - e^{-u/2} = u·e^{S}`, multiplying by `e^{-u/2}` gives
`1 - e^{-u} = u·e^{-u/2 + S}`. -/
private theorem one_sub_cexp_neg_aux (u S : ℂ)
    (h : Complex.exp (u / 2) - Complex.exp (-u / 2) = u * Complex.exp S) :
    1 - Complex.exp (-u) = u * Complex.exp (-u / 2 + S) := by
  have h1 : Complex.exp (-u / 2) * Complex.exp (u / 2) = 1 := by
    rw [← Complex.exp_add, show -u / 2 + u / 2 = 0 by ring, Complex.exp_zero]
  have h2 : Complex.exp (-u / 2) * Complex.exp (-u / 2) = Complex.exp (-u) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc 1 - Complex.exp (-u)
      = Complex.exp (-u / 2) *
          (Complex.exp (u / 2) - Complex.exp (-u / 2)) := by
        rw [mul_sub, h1, h2]
    _ = Complex.exp (-u / 2) * (u * Complex.exp S) := by rw [h]
    _ = u * Complex.exp (-u / 2 + S) := by
        rw [Complex.exp_add]
        ring

/-! ## The expansion -/

/-- **The basic logarithmic expansion, branch-free multiplicative form**
(`lem:basic-bernoulli-log`, equation (19.1)): for every complex `u` with
`‖u‖ < 2π`,

`1 - exp (-u) = u · exp (-u/2 + ∑' r, c_r · u^{2(r+1)})`,

with `c_r = bernoulliLogCoeff r`.  Unlike the source's quotient this is valid
at `u = 0` too, both sides being `0`. -/
theorem one_sub_cexp_neg {u : ℂ} (hu : ‖u‖ < 2 * π) :
    1 - Complex.exp (-u) =
      u * Complex.exp (-u / 2 +
        ∑' r : ℕ, (bernoulliLogCoeff r : ℂ) * u ^ (2 * (r + 1))) := by
  have hpipos : (0 : ℝ) < 2 * π := by
    have := Real.pi_pos
    linarith
  have hx : ‖Complex.I * u / (2 * (π : ℂ))‖ < 1 := by
    rw [norm_rot u]
    exact (div_lt_one hpipos).mpr hu
  have hsinc := complexSinc_pi_mul_eq_cexp hx
  rw [pi_mul_rot u] at hsinc
  have hser : (-∑' r : ℕ, (evenZeta (r + 1) : ℂ) *
        (Complex.I * u / (2 * (π : ℂ))) ^ (2 * (r + 1)) / ((r : ℂ) + 1)) =
      ∑' r : ℕ, (bernoulliLogCoeff r : ℂ) * u ^ (2 * (r + 1)) := by
    rw [← tsum_neg]
    exact tsum_congr fun r => neg_sincZetaTerm_eq_bernoulliLogTerm u r
  rw [hser] at hsinc
  have hmul := mul_complexSinc_I_div_two u
  rw [hsinc] at hmul
  exact one_sub_cexp_neg_aux u _ hmul.symm

/-- The quotient form of the expansion for `u ≠ 0`: this is the source's
left-hand side `(1 - e^{-u})/u`, exponentiated rather than logarithmed so
that no branch has to be chosen. -/
theorem one_sub_cexp_neg_div {u : ℂ} (hu : ‖u‖ < 2 * π) (hu0 : u ≠ 0) :
    (1 - Complex.exp (-u)) / u =
      Complex.exp (-u / 2 +
        ∑' r : ℕ, (bernoulliLogCoeff r : ℂ) * u ^ (2 * (r + 1))) := by
  rw [one_sub_cexp_neg hu, mul_div_cancel_left₀ _ hu0]

/-! ## Convergence -/

/-- An elementary rearrangement: `a·P ≤ Z` upgrades to `a·b ≤ Z·(b/P)`. -/
private theorem le_mul_div_of_mul_le {a b P Z : ℝ} (hP : 0 < P) (hb : 0 ≤ b)
    (h : a * P ≤ Z) : a * b ≤ Z * (b / P) := by
  have hnn : (0 : ℝ) ≤ b / P := div_nonneg hb hP.le
  have hstep : a * P * (b / P) ≤ Z * (b / P) :=
    mul_le_mul_of_nonneg_right h hnn
  have h1 : a * P * (b / P) = a * b * (P / P) := by ring
  rw [h1, div_self (ne_of_gt hP), mul_one] at hstep
  exact hstep

/-- **The explicit geometric majorant.**  For every complex `u` and every
`r`, `‖c_r · u^{2(r+1)}‖ ≤ (π²/6) · (‖u‖/(2π))^{2(r+1)}`.  The constant
`π²/6 = ζ(2)` is the uniform bound on the even zeta values; the source
records no majorant at all. -/
theorem norm_bernoulliLogTerm_le (u : ℂ) (r : ℕ) :
    ‖(bernoulliLogCoeff r : ℂ) * u ^ (2 * (r + 1))‖ ≤
      π ^ 2 / 6 * (‖u‖ / (2 * π)) ^ (2 * (r + 1)) := by
  have hpipos : (0 : ℝ) < 2 * π := by
    have := Real.pi_pos
    linarith
  have hP : (0 : ℝ) < (2 * π) ^ (2 * (r + 1)) := pow_pos hpipos _
  have hrnn : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg (α := ℝ) r
  have hrpos : (0 : ℝ) < (r : ℝ) + 1 := by linarith
  have hpos : (0 : ℝ) < ((r : ℝ) + 1) * (2 * π) ^ (2 * (r + 1)) :=
    mul_pos hrpos hP
  have hsgn : |(-1 : ℝ) ^ r| = 1 := by
    rw [abs_pow, abs_neg, abs_one, one_pow]
  have habs : |(bernoulliLogCoeff r : ℝ)| *
      (((r : ℝ) + 1) * (2 * π) ^ (2 * (r + 1))) = evenZeta (r + 1) := by
    have h1 : |evenZeta (r + 1)| = |(bernoulliLogCoeff r : ℝ)| *
        (((r : ℝ) + 1) * (2 * π) ^ (2 * (r + 1))) := by
      rw [evenZeta_eq_bernoulliLogCoeff r, abs_mul, abs_mul, hsgn, one_mul,
        abs_of_pos hpos]
    rw [← h1]
    exact abs_of_pos (evenZeta_pos (by omega))
  have hzle : evenZeta (r + 1) ≤ π ^ 2 / 6 := by
    rw [← evenZeta_one]
    exact evenZeta_anti (by omega) (by omega)
  have hkey : |(bernoulliLogCoeff r : ℝ)| * (2 * π) ^ (2 * (r + 1)) ≤
      π ^ 2 / 6 := by
    have hstep : |(bernoulliLogCoeff r : ℝ)| * (2 * π) ^ (2 * (r + 1)) ≤
        |(bernoulliLogCoeff r : ℝ)| *
          (((r : ℝ) + 1) * (2 * π) ^ (2 * (r + 1))) := by
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      exact le_mul_of_one_le_left hP.le (by linarith)
    rw [habs] at hstep
    exact hstep.trans hzle
  rw [norm_mul, norm_pow, Complex.norm_ratCast, div_pow]
  exact le_mul_div_of_mul_le hP (pow_nonneg (norm_nonneg u) _) hkey

/-- **The source's convergence claim** "the series converges for `|x| < 2π`",
over `ℂ`: the Bernoulli series of (19.1) is summable on the open disk of
radius `2π`. -/
theorem summable_bernoulliLogTerm {u : ℂ} (hu : ‖u‖ < 2 * π) :
    Summable fun r : ℕ => (bernoulliLogCoeff r : ℂ) * u ^ (2 * (r + 1)) := by
  have hpipos : (0 : ℝ) < 2 * π := by
    have := Real.pi_pos
    linarith
  have hq0 : (0 : ℝ) ≤ ‖u‖ / (2 * π) := div_nonneg (norm_nonneg u) hpipos.le
  have hq1 : ‖u‖ / (2 * π) < 1 := (div_lt_one hpipos).mpr hu
  have hq2 : (‖u‖ / (2 * π)) ^ 2 < 1 := pow_lt_one₀ hq0 hq1 two_ne_zero
  have hq2nn : (0 : ℝ) ≤ (‖u‖ / (2 * π)) ^ 2 := sq_nonneg _
  have hgeo : Summable fun r : ℕ =>
      π ^ 2 / 6 * (‖u‖ / (2 * π)) ^ (2 * (r + 1)) := by
    have hbase := (summable_geometric_of_lt_one hq2nn hq2).mul_left (π ^ 2 / 6)
    have hshift := (summable_nat_add_iff 1).mpr hbase
    refine hshift.congr fun r => ?_
    show π ^ 2 / 6 * ((‖u‖ / (2 * π)) ^ 2) ^ (r + 1) =
      π ^ 2 / 6 * (‖u‖ / (2 * π)) ^ (2 * (r + 1))
    rw [← pow_mul]
  exact Summable.of_norm (Summable.of_nonneg_of_le (fun r => norm_nonneg _)
    (fun r => norm_bernoulliLogTerm_le u r) hgeo)

/-! ## The real statement (19.1) -/

/-- The Bernoulli series of (19.1) is a coercion of the real series. -/
theorem ofReal_bernoulliLogSum (x : ℝ) :
    ((∑' r : ℕ, (bernoulliLogCoeff r : ℝ) * x ^ (2 * (r + 1)) : ℝ) : ℂ) =
      ∑' r : ℕ, (bernoulliLogCoeff r : ℂ) * ((x : ℝ) : ℂ) ^ (2 * (r + 1)) := by
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun r => ?_
  push_cast
  ring

/-- **The source's convergence claim** over `ℝ`: the series of (19.1)
converges for `|x| < 2π`. -/
theorem summable_bernoulliLogTerm_real {x : ℝ} (hx : |x| < 2 * π) :
    Summable fun r : ℕ => (bernoulliLogCoeff r : ℝ) * x ^ (2 * (r + 1)) := by
  have hxc : ‖((x : ℝ) : ℂ)‖ < 2 * π := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hx
  have h := summable_bernoulliLogTerm hxc
  have h2 : Summable fun r : ℕ =>
      (((bernoulliLogCoeff r : ℝ) * x ^ (2 * (r + 1)) : ℝ) : ℂ) := by
    refine h.congr fun r => ?_
    push_cast
    ring
  exact Complex.summable_ofReal.mp h2

/-- Descending the multiplicative identity to real arguments:
`1 - e^{-x} = x · exp (-x/2 + ∑' r, c_r x^{2(r+1)})` for `|x| < 2π`.  In
particular `(1 - e^{-x})/x` is a positive real for every real `x ≠ 0` in the
disk, which is what makes the real logarithm of (19.1) honest. -/
theorem one_sub_rexp_neg {x : ℝ} (hx : |x| < 2 * π) :
    1 - Real.exp (-x) =
      x * Real.exp (-x / 2 +
        ∑' r : ℕ, (bernoulliLogCoeff r : ℝ) * x ^ (2 * (r + 1))) := by
  have hxc : ‖((x : ℝ) : ℂ)‖ < 2 * π := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hx
  have h := one_sub_cexp_neg (u := ((x : ℝ) : ℂ)) hxc
  rw [← ofReal_bernoulliLogSum x] at h
  refine Complex.ofReal_injective ?_
  simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_exp,
    Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_add,
    Complex.ofReal_div, Complex.ofReal_ofNat]
  exact h

/-- **Equation (19.1)** (`lem:basic-bernoulli-log`) literally: for real `x`
with `x ≠ 0` and `|x| < 2π`,

`log ((1 - e^{-x}) / x) = -x/2 + ∑_{r ≥ 1} B_{2r} x^{2r} / (2r (2r)!)`,

the logarithm being the real one and the sum over `r : ℕ` of
`bernoulliLogCoeff r * x ^ (2 * (r + 1))` realizing `∑_{r ≥ 1}`. -/
theorem log_one_sub_rexp_neg_div {x : ℝ} (hx0 : x ≠ 0) (hx : |x| < 2 * π) :
    Real.log ((1 - Real.exp (-x)) / x) =
      -x / 2 + ∑' r : ℕ, (bernoulliLogCoeff r : ℝ) * x ^ (2 * (r + 1)) := by
  rw [one_sub_rexp_neg hx, mul_div_cancel_left₀ _ hx0, Real.log_exp]

end Fabius
