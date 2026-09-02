import FabiusFunction.QGamma
import FabiusFunction.QPochhammerLogDerivative
import Mathlib.Analysis.Complex.RealDeriv

/-!
# The logarithmic derivative of `Γ_q`

For `0 < q < 1` and `x > 0`,

`d/dx log Γ_q(x) = -log(1-q) + (log q) ∑_{n≥0} q^{n+x} / (1 - q^{n+x})`.

The real function `x ↦ (q^x;q)_∞` is the composition of `x ↦ q^x` with the real restriction of
the complex-analytic symbol `a ↦ (a;q)_∞`, whose derivative `-(a;q)_∞ ∑_j q^j/(1-aq^j)` is
known (`hasDerivAt_qPochhammerInfIn`); the real restriction is obtained through
`HasDerivAt.real_of_complex` once `(a;q)_∞` is seen to be real for real `a, q`.  The
logarithm of `Γ_q(x) = (q;q)_∞ (1-q)^{1-x}/(q^x;q)_∞` then differentiates termwise.

## Main declarations

* `ofReal_qPochhammerInfIn`: the complex symbol of real arguments is real.
* `hasDerivAt_qPochhammerInfIn_real`: the real derivative of `a ↦ (a;q)_∞`.
* `hasDerivAt_log_qGamma`: the logarithmic derivative of `Γ_q`.
-/

set_option autoImplicit false

open Filter Topology

namespace Fabius

/-- The complex `q`-Pochhammer symbol of real arguments is the real one. -/
theorem ofReal_qPochhammerInfIn {a q : ℝ} (hq : ‖q‖ < 1) :
    ((qPochhammerInfIn a q : ℝ) : ℂ) = qPochhammerInfIn (a : ℂ) (q : ℂ) := by
  have h := (hasProd_qPochhammerInfIn a hq).map Complex.ofRealHom.toMonoidHom
    Complex.continuous_ofReal
  simp [Function.comp_def] at h
  exact h.tprod_eq.symm

variable {q : ℝ}

/-- **The real derivative of `a ↦ (a;q)_∞`**: `-(a;q)_∞ ∑_j q^j/(1-aq^j)` for `|a| < 1`. -/
theorem hasDerivAt_qPochhammerInfIn_real (hq : ‖q‖ < 1) {a : ℝ} (ha : ‖a‖ < 1) :
    HasDerivAt (fun y : ℝ => qPochhammerInfIn y q)
      (-(qPochhammerInfIn a q * ∑' j : ℕ, q ^ j / (1 - a * q ^ j))) a := by
  have hqc : ‖(q : ℂ)‖ < 1 := by rwa [Complex.norm_real]
  have hac : ‖(a : ℂ)‖ < 1 := by rwa [Complex.norm_real]
  have hC := (hasDerivAt_qPochhammerInfIn hqc hac).real_of_complex
  have hfun : (fun t : ℝ => (qPochhammerInfIn (t : ℂ) (q : ℂ)).re) =
      fun t : ℝ => qPochhammerInfIn t q :=
    funext fun t => by rw [← ofReal_qPochhammerInfIn hq, Complex.ofReal_re]
  have hval : (-(qPochhammerInfIn (a : ℂ) (q : ℂ) *
      ∑' j : ℕ, (q : ℂ) ^ j / (1 - (a : ℂ) * (q : ℂ) ^ j))) =
      ((-(qPochhammerInfIn a q * ∑' j : ℕ, q ^ j / (1 - a * q ^ j)) : ℝ) : ℂ) := by
    simp only [Complex.ofReal_neg, Complex.ofReal_mul, ofReal_qPochhammerInfIn hq,
      Complex.ofReal_tsum, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_sub,
      Complex.ofReal_one]
  rw [hfun, hval, Complex.ofReal_re] at hC
  exact hC

/-- **The logarithmic derivative of `Γ_q`**:
`(log Γ_q)'(x) = -log(1-q) + (log q) ∑_n q^{n+x}/(1-q^{n+x})` for `0 < q < 1`, `x > 0`. -/
theorem hasDerivAt_log_qGamma (hq0 : 0 < q) (hq1 : q < 1) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => Real.log (qGamma q y))
      (-Real.log (1 - q) + Real.log q * ∑' n : ℕ, q ^ ((n : ℝ) + x) / (1 - q ^ ((n : ℝ) + x))) x := by
  have hq : ‖q‖ < 1 := norm_lt_one_of_pos_of_lt_one hq0 hq1
  have h1q : 0 < 1 - q := by linarith
  have hP : 0 < qPochhammerInfIn q q := qPochhammerInfIn_self_pos hq0 hq1
  have ha0 : 0 < q ^ x := Real.rpow_pos_of_pos hq0 x
  have ha1 : q ^ x < 1 := Real.rpow_lt_one hq0.le hq1 hx
  have haN : ‖q ^ x‖ < 1 := by rw [Real.norm_of_nonneg ha0.le]; exact ha1
  have hPx : 0 < qPochhammerInfIn (q ^ x) q := qPochhammerInfIn_rpow_pos hq0 hq1 hx
  -- the derivative of `y ↦ (q^y;q)_∞` at `x`
  have hpow : HasDerivAt (fun y : ℝ => q ^ y) (q ^ x * Real.log q) x :=
    (Real.hasStrictDerivAt_const_rpow hq0 x).hasDerivAt
  have hcomp := (hasDerivAt_qPochhammerInfIn_real hq haN).comp x hpow
  -- `log Γ_q(y) = log (q;q)_∞ + (1 - y) log (1 - q) - log (q^y;q)_∞` near `x`
  have hlog : ∀ᶠ y in 𝓝 x, Real.log (qGamma q y) =
      Real.log (qPochhammerInfIn q q) + (1 - y) * Real.log (1 - q) -
        Real.log (qPochhammerInfIn (q ^ y) q) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    have hPy : 0 < qPochhammerInfIn (q ^ y) q := qPochhammerInfIn_rpow_pos hq0 hq1 hy
    have hr : 0 < (1 - q) ^ (1 - y) := Real.rpow_pos_of_pos h1q _
    rw [qGamma, Real.log_mul (div_pos hP hPy).ne' hr.ne', Real.log_div hP.ne' hPy.ne',
      Real.log_rpow h1q]
    ring
  have hD : HasDerivAt (fun y : ℝ => Real.log (qPochhammerInfIn q q) + (1 - y) * Real.log (1 - q) -
      Real.log (qPochhammerInfIn (q ^ y) q))
      (0 + (-1) * Real.log (1 - q) -
        (-(qPochhammerInfIn (q ^ x) q * ∑' j : ℕ, q ^ j / (1 - q ^ x * q ^ j)) *
          (q ^ x * Real.log q)) / qPochhammerInfIn (q ^ x) q) x := by
    refine ((hasDerivAt_const x _).add (((hasDerivAt_id x).const_sub 1).mul_const _)).sub
      (hcomp.log hPx.ne')
  refine (hD.congr_of_eventuallyEq hlog).congr_deriv ?_
  -- simplify the derivative value
  have hterm : ∀ j : ℕ, q ^ ((j : ℝ) + x) = q ^ x * q ^ j := fun j => by
    rw [Real.rpow_add hq0, Real.rpow_natCast, mul_comm]
  simp_rw [hterm, mul_div_assoc, tsum_mul_left]
  have hPx' := hPx.ne'
  field_simp
  all_goals ring

end Fabius
