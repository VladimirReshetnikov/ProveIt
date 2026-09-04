import FabiusFunction.PrincipalLambertW
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Exact inversion of the linear–logarithmic phase

The transseries volume's `p0:thm:lambert-core` solves the dominant block

`Φ₀(X) = a X + b log X = L`   (`X > 0`)

in closed form.  Its part (2) is the substitution `W = (a/b) X`, which turns the
equation into the Lambert equation `W e^W = z(L)` with `z(L) = (a/b) e^{L/b}`;
part (3) is the branch rule; part (4) the slope identities.

The substitution is the content, and it is worth isolating exactly why it works:
dividing by `b` and exponentiating turns `(a/b)X + log X = L/b` into
`e^{(a/b)X} · X = e^{L/b}`, and *no logarithm of a negative number occurs*, so
the step is uniform in the sign of `b`.  `linLogCore_eq_iff` below is that
equivalence, and it is an `iff` at every nonzero `a`, `b` and every positive `X`
— it is not restricted to a branch, and not restricted to a sign.

The branch rule is then a separate, and genuinely sign-dependent, question.
This module settles the case `b > 0`, where `z(L) > 0`, `Φ₀` is strictly
increasing on `(0,∞)`, and there is exactly one positive solution for every real
`L`, given by the principal branch.

## Main results

* `Fabius.linLogCore_eq_iff`: `aX + b log X = L ↔ W e^W = z(L)` with
  `W = (a/b) X`, for any nonzero `a, b` and any `X > 0`.  This is
  `p0:eq:core-W-equation`.
* `Fabius.linLogCoreRoot`: `X = (b/a) W₀(z(L))`, which is `p0:eq:core-lambert`
  at `k = 0`.
* `Fabius.linLogCore_linLogCoreRoot`: it solves the equation, for `a, b > 0`.
* `Fabius.strictMonoOn_linLogCore` and `Fabius.linLogCoreRoot_unique`: for
  `a, b > 0` it is the *only* positive solution — the first bullet of the branch
  rule `p0:eq:core-threshold`'s preamble.
* `Fabius.hasDerivAt_linLogCore` and `Fabius.linLogCore_slope_eq`: the slope
  identities `p0:eq:core-slope`, `Φ₀'(X) = a + b/X = a(1+W)/W`.

Not formalized here: the case `b < 0`, where `Φ₀` has an interior critical point
at `X = |b|/a`, the threshold `L_c = |b|(1 - log(|b|/a))` appears, and there are
two positive solutions above it — one on each branch.  That needs the lower real
branch as well, and the order reversal of `W ↦ (b/a) W`.
-/

set_option autoImplicit false

namespace Fabius

open Set

/-- `z(L) = (a/b) e^{L/b}`, the Lambert argument of `p0:eq:core-W-equation`. -/
noncomputable def linLogCoreArg (a b L : ℝ) : ℝ := a / b * Real.exp (L / b)

/-- `X = (b/a) W₀(z(L))`, the principal-branch root of `p0:eq:core-lambert`. -/
noncomputable def linLogCoreRoot (a b L : ℝ) : ℝ :=
  b / a * principalLambertW (linLogCoreArg a b L)

/-- The substitution `W = (a/b) X` turns the linear–logarithmic equation into the
Lambert equation.  Uniform in the sign of `b`: no logarithm of a negative number
is taken anywhere in the argument. -/
theorem linLogCore_eq_iff {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) {X : ℝ} (hX : 0 < X)
    (L : ℝ) :
    a * X + b * Real.log X = L ↔
      a / b * X * Real.exp (a / b * X) = a / b * Real.exp (L / b) := by
  have hab : a / b ≠ 0 := div_ne_zero ha hb
  constructor
  · intro h
    have h1 : a / b * X + Real.log X = L / b := by
      field_simp
      linarith
    have h2 : Real.exp (a / b * X + Real.log X) = Real.exp (L / b) := by rw [h1]
    rw [Real.exp_add, Real.exp_log hX] at h2
    calc a / b * X * Real.exp (a / b * X)
        = a / b * (Real.exp (a / b * X) * X) := by ring
      _ = a / b * Real.exp (L / b) := by rw [h2]
  · intro h
    have h2 : a / b * (Real.exp (a / b * X) * X) = a / b * Real.exp (L / b) := by
      rw [← h]; ring
    have h3 : Real.exp (a / b * X) * X = Real.exp (L / b) := mul_left_cancel₀ hab h2
    have h4 : Real.exp (a / b * X + Real.log X) = Real.exp (L / b) := by
      rw [Real.exp_add, Real.exp_log hX]
      exact h3
    have h5 : a / b * X + Real.log X = L / b := Real.exp_eq_exp.mp h4
    field_simp at h5
    linarith

private theorem neg_exp_neg_one_le_zero : -Real.exp (-1) ≤ (0:ℝ) := by
  have := Real.exp_pos (-1)
  linarith

/-- For `a, b > 0` the Lambert argument is positive, so the principal branch is
defined there and takes a positive value. -/
theorem principalLambertW_linLogCoreArg_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (L : ℝ) :
    0 < principalLambertW (linLogCoreArg a b L) := by
  have hz : 0 < linLogCoreArg a b L := by
    rw [linLogCoreArg]
    positivity
  have h := principalLambertW_strictMonoOn (mem_Ici.mpr neg_exp_neg_one_le_zero)
    (mem_Ici.mpr (le_of_lt (lt_of_le_of_lt neg_exp_neg_one_le_zero hz))) hz
  rwa [principalLambertW_zero] at h

theorem linLogCoreRoot_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (L : ℝ) :
    0 < linLogCoreRoot a b L := by
  have hW := principalLambertW_linLogCoreArg_pos ha hb L
  rw [linLogCoreRoot]
  positivity

/-- `p0:eq:core-lambert` at `k = 0`: the principal-branch root solves the
linear–logarithmic equation. -/
theorem linLogCore_linLogCoreRoot {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (L : ℝ) :
    a * linLogCoreRoot a b L + b * Real.log (linLogCoreRoot a b L) = L := by
  have hz : -Real.exp (-1) ≤ linLogCoreArg a b L := by
    refine le_trans neg_exp_neg_one_le_zero ?_
    rw [linLogCoreArg]
    positivity
  rw [linLogCore_eq_iff ha.ne' hb.ne' (linLogCoreRoot_pos ha hb L)]
  have hX : a / b * linLogCoreRoot a b L = principalLambertW (linLogCoreArg a b L) := by
    rw [linLogCoreRoot]
    field_simp
  rw [hX]
  exact principalLambertW_mul_exp hz

/-- For `a, b > 0` the phase is strictly increasing on `(0,∞)`. -/
theorem strictMonoOn_linLogCore {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    StrictMonoOn (fun X : ℝ => a * X + b * Real.log X) (Ioi 0) := by
  intro x hx y _ hxy
  have hx0 : 0 < x := mem_Ioi.mp hx
  have hlog : Real.log x < Real.log y := Real.log_lt_log hx0 hxy
  have hlin : a * x < a * y := by nlinarith
  nlinarith

/-- For `a, b > 0` the principal-branch root is the *unique* positive solution. -/
theorem linLogCoreRoot_unique {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (L : ℝ)
    {X : ℝ} (hX : 0 < X) (h : a * X + b * Real.log X = L) :
    X = linLogCoreRoot a b L := by
  refine (strictMonoOn_linLogCore ha hb).injOn (mem_Ioi.mpr hX)
    (mem_Ioi.mpr (linLogCoreRoot_pos ha hb L)) ?_
  show a * X + b * Real.log X
      = a * linLogCoreRoot a b L + b * Real.log (linLogCoreRoot a b L)
  rw [h, linLogCore_linLogCoreRoot ha hb]

/-- The first slope identity of `p0:eq:core-slope`: `Φ₀'(X) = a + b/X`. -/
theorem hasDerivAt_linLogCore (a b : ℝ) {X : ℝ} (hX : 0 < X) :
    HasDerivAt (fun Y : ℝ => a * Y + b * Real.log Y) (a + b / X) X := by
  have h1 : HasDerivAt (fun Y : ℝ => a * Y) a X := by
    simpa using (hasDerivAt_id X).const_mul a
  have h2 : HasDerivAt (fun Y : ℝ => b * Real.log Y) (b / X) X := by
    have h := (Real.hasDerivAt_log hX.ne').const_mul b
    simpa [div_eq_mul_inv] using h
  exact h1.add h2

/-- The second slope identity of `p0:eq:core-slope`: in the Lambert variable
`W = (a/b) X`, the slope is `a (1 + W) / W`. -/
theorem linLogCore_slope_eq {a b X : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hX : X ≠ 0) :
    a + b / X = a * (1 + a / b * X) / (a / b * X) := by
  field_simp
  ring

end Fabius
