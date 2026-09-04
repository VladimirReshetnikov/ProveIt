import FabiusFunction.LambertWAnalytic
import FabiusFunction.PrincipalLambertWAtTop

/-!
# The Wright omega function

The transseries volume's `plt:prop:mot-omega-basic`: the map `Φ(y) = y + log y`
is a strictly increasing bijection of `(0, ∞)` onto `ℝ`, its inverse `ω`
satisfies `ω(X) + log ω(X) = X`, it is strictly increasing with `ω(X) → ∞`, it
obeys the envelope `X - log X ≤ ω(X) ≤ X` for `X ≥ 1`, and it is related to the
principal Lambert branch by `W₀(z) = ω(log z)`.

Rather than build the inverse from scratch, `ω` is *defined* by that last
relation, `ω(X) = W₀(e^X)`, which makes the identification with `W₀` definitional
and every other clause a short consequence of the Lambert API already in the
corpus.  In particular the defining equation is `principalLambertW_add_log` read
at `x = e^X`.

The envelope is proved here in a sharper form than the volume states it: the
upper bound `ω(X) ≤ X` needs only `X ≥ 1`, and the lower bound then follows from
it by monotonicity of `log`, with no appeal to the asymptotics of `W`.

Real analyticity is inherited from the analytic principal Lambert branch: the
exponential image is contained strictly above the branch point, so analytic
composition applies globally.
-/

set_option autoImplicit false

namespace Fabius

open Real

/-- **Wright's omega**, defined through the principal Lambert branch. -/
noncomputable def wrightOmega (X : ℝ) : ℝ := principalLambertW (Real.exp X)

/-- **Real analyticity of Wright omega.**  The exponential image lies strictly
above the principal Lambert branch point, so analyticity follows by composition
with the real exponential. -/
theorem analyticAt_wrightOmega (X : ℝ) :
    AnalyticAt ℝ wrightOmega X := by
  have hdom : -Real.exp (-1) < Real.exp X :=
    (neg_lt_zero.mpr (Real.exp_pos (-1))).trans (Real.exp_pos X)
  change AnalyticAt ℝ (fun x : ℝ => principalLambertW (Real.exp x)) X
  exact (analyticAt_principalLambertW hdom).comp
    (analyticAt_rexp (x := X))

/-- `ω` is positive. -/
theorem wrightOmega_pos (X : ℝ) : 0 < wrightOmega X :=
  principalLambertW_pos (Real.exp_pos X)

/-- **`plt:eq:mot-omega-equation`**: `ω(X) + log ω(X) = X`, so `ω` inverts
`Φ(y) = y + log y`. -/
theorem wrightOmega_add_log (X : ℝ) : wrightOmega X + Real.log (wrightOmega X) = X := by
  have h := principalLambertW_add_log (x := Real.exp X) (Real.exp_pos X)
  rwa [Real.log_exp] at h

/-- **The Lambert relation**: `W₀(z) = ω(log z)` for `z > 0`. -/
theorem principalLambertW_eq_wrightOmega_log {z : ℝ} (hz : 0 < z) :
    principalLambertW z = wrightOmega (Real.log z) := by
  rw [wrightOmega, Real.exp_log hz]

/-- `Φ` is a left inverse of `ω`: this is the defining equation restated. -/
theorem wrightOmega_leftInverse (y : ℝ) (hy : 0 < y) :
    wrightOmega (y + Real.log y) = y := by
  have hpos : 0 < y * Real.exp y := mul_pos hy (Real.exp_pos y)
  have hz : -Real.exp (-1) ≤ y * Real.exp y := by
    have := Real.exp_pos (-1)
    linarith
  have hexp : Real.exp (y + Real.log y) = y * Real.exp y := by
    rw [Real.exp_add, Real.exp_log hy]
    ring
  rw [wrightOmega, hexp]
  exact (principalLambertW_unique hz (by linarith) rfl).symm

/-- `ω` is strictly increasing. -/
theorem wrightOmega_strictMono : StrictMono wrightOmega := by
  intro a b hab
  have ha : -Real.exp (-1) ≤ Real.exp a := by
    have := Real.exp_pos (-1)
    have := Real.exp_pos a
    linarith
  have hb : -Real.exp (-1) ≤ Real.exp b := by
    have := Real.exp_pos (-1)
    have := Real.exp_pos b
    linarith
  exact principalLambertW_strictMonoOn (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr hb)
    (Real.exp_lt_exp.mpr hab)

/-- `ω(1) = 1`, the anchor of the envelope. -/
theorem wrightOmega_one : wrightOmega 1 = 1 := by
  have h := wrightOmega_leftInverse 1 one_pos
  rwa [Real.log_one, add_zero] at h

/-- `1 ≤ ω(X)` for `X ≥ 1`. -/
theorem one_le_wrightOmega {X : ℝ} (hX : 1 ≤ X) : 1 ≤ wrightOmega X := by
  rw [← wrightOmega_one]
  exact wrightOmega_strictMono.monotone hX

/-- **`plt:eq:mot-envelope`, upper half**: `ω(X) ≤ X` for `X ≥ 1`. -/
theorem wrightOmega_le_self {X : ℝ} (hX : 1 ≤ X) : wrightOmega X ≤ X := by
  have heq := wrightOmega_add_log X
  have hlog : 0 ≤ Real.log (wrightOmega X) := Real.log_nonneg (one_le_wrightOmega hX)
  linarith

/-- **`plt:eq:mot-envelope`, lower half**: `X - log X ≤ ω(X)` for `X ≥ 1`. -/
theorem sub_log_le_wrightOmega {X : ℝ} (hX : 1 ≤ X) : X - Real.log X ≤ wrightOmega X := by
  have heq := wrightOmega_add_log X
  have hle : Real.log (wrightOmega X) ≤ Real.log X :=
    Real.log_le_log (wrightOmega_pos X) (wrightOmega_le_self hX)
  linarith

/-- **`plt:eq:mot-envelope`**, both halves. -/
theorem wrightOmega_envelope {X : ℝ} (hX : 1 ≤ X) :
    X - Real.log X ≤ wrightOmega X ∧ wrightOmega X ≤ X :=
  ⟨sub_log_le_wrightOmega hX, wrightOmega_le_self hX⟩

/-- A global linear lower bound, from `log y ≤ y - 1`: `(X + 1)/2 ≤ ω(X)` for
every real `X`, with no hypothesis at all.  It is weaker than the envelope where
the envelope applies, but it holds everywhere and is enough for divergence. -/
theorem add_one_div_two_le_wrightOmega (X : ℝ) : (X + 1) / 2 ≤ wrightOmega X := by
  have heq := wrightOmega_add_log X
  have hlog : Real.log (wrightOmega X) ≤ wrightOmega X - 1 :=
    Real.log_le_sub_one_of_pos (wrightOmega_pos X)
  linarith

/-- `ω(X) → ∞` as `X → ∞`. -/
theorem tendsto_wrightOmega_atTop :
    Filter.Tendsto wrightOmega Filter.atTop Filter.atTop := by
  have hlin : Filter.Tendsto (fun X : ℝ => (X + 1) / 2) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_div_const two_pos
      (Filter.tendsto_atTop_add_const_right _ 1 Filter.tendsto_id)
  exact Filter.tendsto_atTop_mono add_one_div_two_le_wrightOmega hlin

end Fabius
