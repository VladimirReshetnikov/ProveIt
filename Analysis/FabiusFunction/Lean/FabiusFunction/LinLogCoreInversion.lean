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

The branch rule is then a separate, and genuinely sign-dependent, question, and
both signs are settled here.

For `b > 0`: `z(L) > 0`, `Φ₀` is strictly increasing on `(0,∞)`, and there is
exactly one positive solution for every real `L`, on the **principal** branch.

For `b < 0`: `Φ₀` has an interior critical point at `X = |b|/a`, whose critical
value is the threshold `L_c = |b|(1 - log(|b|/a))`.  Above `L_c` — and, as an
equivalence, only above it — the Lambert argument lies in `(-e⁻¹, 0)`, where
both real branches are defined, and there are two positive solutions:
`(b/a) W₀(z)` below `|b|/a` and `(b/a) W₋₁(z)` above it.

## Main results

* `Fabius.linLogCore_eq_iff`: `aX + b log X = L ↔ W e^W = z(L)` with
  `W = (a/b) X`, for any nonzero `a, b` and any `X > 0`.  This is
  `p0:eq:core-W-equation`, and it is branch-free and sign-free.
* `Fabius.linLogCoreRoot`: `X = (b/a) W₀(z(L))` — the **principal** branch.
* `Fabius.linLogCore_linLogCoreRoot`: it solves the equation, for `a, b > 0`.
* `Fabius.strictMonoOn_linLogCore` and `Fabius.linLogCoreRoot_unique`: for
  `a, b > 0` it is the *only* positive solution.
* `Fabius.hasDerivAt_linLogCore` and `Fabius.linLogCore_slope_eq`: the slope
  identities `p0:eq:core-slope`, `Φ₀'(X) = a + b/X = a(1+W)/W`.
* `Fabius.linLogCoreThreshold` and `Fabius.linLogCore_critical`: `L_c`, and the
  fact that it is the critical value `Φ₀(|b|/a)`.
* `Fabius.linLogCoreArg_mem_Ioo_iff`: for `b < 0`, `z(L) ∈ (-e⁻¹,0) ↔ L > L_c`
  — an equivalence, so the threshold is necessary as well as sufficient.
* `Fabius.linLogCoreRootLower`: `X = (b/a) W₋₁(z(L))` — the **lower** branch.
* `Fabius.linLogCore_linLogCoreRoot_of_neg` and
  `Fabius.linLogCore_linLogCoreRootLower`: for `b < 0` both roots solve the
  equation.
* `Fabius.linLogCoreRoot_lt_critical`, `Fabius.critical_lt_linLogCoreRootLower`
  and `Fabius.linLogCoreRoot_ne_linLogCoreRootLower`: the separation
  `X₀ < |b|/a < X₋₁`, hence distinctness.  This is where the order reversal of
  `W ↦ (b/a) W` is used: `-1 < W₀(z)` and `W₋₁(z) < -1` multiplied by the
  *negative* `b/a`, so the branch with the larger `W` gives the smaller `X`.

Not formalized here: the asymptotic clause `X = L/a + O(log L)` as `L → +∞`, and
the complex reading with a general branch `W_k`.
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

/-- For `a, b > 0` the principal-branch root is positive, so it lies in the
domain `(0,∞)` on which the phase is defined. -/
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

/-! ### The case `b < 0`: a threshold, and two roots on two branches -/

/-- The threshold `L_c = |b| (1 - log(|b|/a))` of `p0:eq:core-threshold`. -/
noncomputable def linLogCoreThreshold (a b : ℝ) : ℝ := -b * (1 - Real.log (-b / a))

/-- `X = -b/a` is the critical point of `Φ₀` when `b < 0`, and the threshold is
its critical value: `L_c = Φ₀(|b|/a)`. -/
theorem linLogCore_critical {a b : ℝ} (ha : 0 < a) :
    a * (-b / a) + b * Real.log (-b / a) = linLogCoreThreshold a b := by
  have h : a * (-b / a) = -b := by field_simp
  rw [linLogCoreThreshold, h]
  ring

/-- `p0:eq:core-threshold`: for `b < 0` the Lambert argument lands in the
two-branch window `(-e⁻¹, 0)` exactly above the threshold. -/
theorem linLogCoreArg_mem_Ioo_iff {a b : ℝ} (ha : 0 < a) (hb : b < 0) (L : ℝ) :
    linLogCoreArg a b L ∈ Ioo (-Real.exp (-1)) 0 ↔ linLogCoreThreshold a b < L := by
  have hbpos : (0:ℝ) < -b := by linarith
  have hfrac : (0:ℝ) < a / -b := div_pos ha hbpos
  have hneg : linLogCoreArg a b L < 0 := by
    rw [linLogCoreArg]
    exact mul_neg_of_neg_of_pos (div_neg_of_pos_of_neg ha hb) (Real.exp_pos _)
  have hthr : linLogCoreThreshold a b = b * (Real.log (-b / a) - 1) := by
    rw [linLogCoreThreshold]
    ring
  have step1 : (-Real.exp (-1) < linLogCoreArg a b L)
      ↔ (a / -b * Real.exp (L / b) < Real.exp (-1)) := by
    rw [linLogCoreArg, show a / b * Real.exp (L / b)
        = -(a / -b * Real.exp (L / b)) from by field_simp]
    exact neg_lt_neg_iff
  have step2 : (a / -b * Real.exp (L / b) < Real.exp (-1))
      ↔ (L / b < Real.log (-b / a) - 1) := by
    rw [show a / -b * Real.exp (L / b) = Real.exp (Real.log (a / -b) + L / b) from by
      rw [Real.exp_add, Real.exp_log hfrac], Real.exp_lt_exp]
    have hlog : Real.log (a / -b) = -Real.log (-b / a) := by
      rw [← Real.log_inv]
      congr 1
      field_simp
    rw [hlog]
    constructor <;> intro h <;> linarith
  have step3 : (L / b < Real.log (-b / a) - 1) ↔ (linLogCoreThreshold a b < L) := by
    rw [hthr, div_lt_iff_of_neg' hb]
  rw [mem_Ioo, and_iff_left hneg]
  exact step1.trans (step2.trans step3)

/-- `X = (b/a) W₋₁(z(L))`, the *lower*-branch root of `p0:eq:core-lambert-minus`. -/
noncomputable def linLogCoreRootLower (a b L : ℝ) : ℝ :=
  b / a * lowerLambertW (linLogCoreArg a b L)

/-- Inside the two-branch window the principal branch is negative, which is what
makes `(b/a) W₀(z)` positive when `b < 0`. -/
theorem principalLambertW_linLogCoreArg_neg {a b L : ℝ}
    (hz : linLogCoreArg a b L ∈ Ioo (-Real.exp (-1)) 0) :
    principalLambertW (linLogCoreArg a b L) < 0 := by
  have h := principalLambertW_strictMonoOn (mem_Ici.mpr hz.1.le)
    (mem_Ici.mpr neg_exp_neg_one_le_zero) hz.2
  rwa [principalLambertW_zero] at h

/-- For `b < 0`, above the threshold, the principal-branch root is positive. -/
theorem linLogCoreRoot_pos_of_neg {a b : ℝ} (ha : 0 < a) (hb : b < 0) {L : ℝ}
    (hz : linLogCoreArg a b L ∈ Ioo (-Real.exp (-1)) 0) :
    0 < linLogCoreRoot a b L := by
  rw [linLogCoreRoot]
  exact mul_pos_of_neg_of_neg (div_neg_of_neg_of_pos hb ha)
    (principalLambertW_linLogCoreArg_neg hz)

/-- For `b < 0`, above the threshold, the lower-branch root is positive. -/
theorem linLogCoreRootLower_pos {a b : ℝ} (ha : 0 < a) (hb : b < 0) {L : ℝ}
    (hz : linLogCoreArg a b L ∈ Ioo (-Real.exp (-1)) 0) :
    0 < linLogCoreRootLower a b L := by
  have hW : lowerLambertW (linLogCoreArg a b L) < -1 := lowerLambertW_lt_neg_one hz
  rw [linLogCoreRootLower]
  exact mul_pos_of_neg_of_neg (div_neg_of_neg_of_pos hb ha) (by linarith)

/-- The smaller of the two roots, on the principal branch. -/
theorem linLogCore_linLogCoreRoot_of_neg {a b : ℝ} (ha : 0 < a) (hb : b < 0) {L : ℝ}
    (hz : linLogCoreArg a b L ∈ Ioo (-Real.exp (-1)) 0) :
    a * linLogCoreRoot a b L + b * Real.log (linLogCoreRoot a b L) = L := by
  rw [linLogCore_eq_iff ha.ne' hb.ne (linLogCoreRoot_pos_of_neg ha hb hz)]
  have hbne : b ≠ 0 := hb.ne
  have hX : a / b * linLogCoreRoot a b L = principalLambertW (linLogCoreArg a b L) := by
    rw [linLogCoreRoot]
    field_simp
  rw [hX]
  exact principalLambertW_mul_exp hz.1.le

/-- The larger of the two roots, on the lower branch: `p0:eq:core-lambert-minus`. -/
theorem linLogCore_linLogCoreRootLower {a b : ℝ} (ha : 0 < a) (hb : b < 0) {L : ℝ}
    (hz : linLogCoreArg a b L ∈ Ioo (-Real.exp (-1)) 0) :
    a * linLogCoreRootLower a b L + b * Real.log (linLogCoreRootLower a b L) = L := by
  rw [linLogCore_eq_iff ha.ne' hb.ne (linLogCoreRootLower_pos ha hb hz)]
  have hbne : b ≠ 0 := hb.ne
  have hX : a / b * linLogCoreRootLower a b L = lowerLambertW (linLogCoreArg a b L) := by
    rw [linLogCoreRootLower]
    field_simp
  rw [hX]
  exact lowerLambertW_mul_exp hz

/-- The two roots straddle the critical point: `X₀ < |b|/a < X₋₁`.  This is what
makes them distinct, and it is where the order reversal of `W ↦ (b/a) W` is
used — the principal branch, whose values are the *larger*, gives the *smaller*
root. -/
theorem linLogCoreRoot_lt_critical {a b : ℝ} (ha : 0 < a) (hb : b < 0) {L : ℝ}
    (hz : linLogCoreArg a b L ∈ Ioo (-Real.exp (-1)) 0) :
    linLogCoreRoot a b L < -b / a := by
  have hW : -1 < principalLambertW (linLogCoreArg a b L) :=
    neg_one_lt_principalLambertW hz.1
  have h := mul_lt_mul_of_neg_left hW (div_neg_of_neg_of_pos hb ha)
  rw [linLogCoreRoot]
  calc b / a * principalLambertW (linLogCoreArg a b L) < b / a * (-1) := h
    _ = -b / a := by ring

/-- The lower-branch root lies above the critical point `|b|/a`. -/
theorem critical_lt_linLogCoreRootLower {a b : ℝ} (ha : 0 < a) (hb : b < 0) {L : ℝ}
    (hz : linLogCoreArg a b L ∈ Ioo (-Real.exp (-1)) 0) :
    -b / a < linLogCoreRootLower a b L := by
  have hW : lowerLambertW (linLogCoreArg a b L) < -1 := lowerLambertW_lt_neg_one hz
  have h := mul_lt_mul_of_neg_left hW (div_neg_of_neg_of_pos hb ha)
  rw [linLogCoreRootLower]
  calc -b / a = b / a * (-1) := by ring
    _ < b / a * lowerLambertW (linLogCoreArg a b L) := h

/-- The two roots are distinct. -/
theorem linLogCoreRoot_ne_linLogCoreRootLower {a b : ℝ} (ha : 0 < a) (hb : b < 0)
    {L : ℝ} (hz : linLogCoreArg a b L ∈ Ioo (-Real.exp (-1)) 0) :
    linLogCoreRoot a b L ≠ linLogCoreRootLower a b L :=
  ne_of_lt (lt_trans (linLogCoreRoot_lt_critical ha hb hz)
    (critical_lt_linLogCoreRootLower ha hb hz))

end Fabius
