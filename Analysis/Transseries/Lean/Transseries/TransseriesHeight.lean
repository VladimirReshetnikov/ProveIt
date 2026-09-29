import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Height wins: powers and logarithms against the next exponential level

The transseries volume's `q0:prop:height`: on the scale of the
polynomial–logarithmic calculus, no product of powers and logarithms competes
with a monomial of greater exponential height,

`x^N (log x)^M = o(e^{εx})`  for every `ε > 0`,

and dually every power of a logarithm is beaten by every positive power,

`(log x)^M = o(x^δ)`  for every `δ > 0`.

Both are assembled from Mathlib's comparisons: `isLittleO_log_rpow_rpow_atTop`
for the logarithm against a power, and `isLittleO_pow_exp_pos_mul_atTop` for a
power against the exponential.  The point of recording them here is that the
volume uses this ordering as the defining property of its scale, so it is worth
having in the corpus in the exact shape the volume states.
-/

set_option autoImplicit false

open Filter Asymptotics Real

namespace Fabius

/-- **`q0:eq:height`, dual half.**  Every power of `log` is `o` of every
positive power of `x`. -/
theorem isLittleO_log_pow_rpow (M : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (fun x : ℝ => Real.log x ^ M) =o[atTop] fun x : ℝ => x ^ δ := by
  have h := isLittleO_log_rpow_rpow_atTop (s := δ) (M : ℝ) hδ
  refine h.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards with x
  rw [Real.rpow_natCast]

/-- The logarithm power is `o` of the first power of `x`. -/
theorem isLittleO_log_pow_id (M : ℕ) :
    (fun x : ℝ => Real.log x ^ M) =o[atTop] fun x : ℝ => x := by
  have h := isLittleO_log_pow_rpow M (δ := 1) one_pos
  refine h.congr' (Eventually.of_forall fun _ => rfl) ?_
  filter_upwards with x
  rw [Real.rpow_one]

/-- **`q0:eq:height`.**  A power times a power of the logarithm is `o` of every
exponential `e^{εx}` with `ε > 0`: height beats the polynomial–logarithmic
scale outright. -/
theorem isLittleO_pow_mul_log_pow_exp (N M : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (fun x : ℝ => x ^ N * Real.log x ^ M) =o[atTop] fun x : ℝ => Real.exp (ε * x) := by
  have hstep : (fun x : ℝ => x ^ N * Real.log x ^ M) =o[atTop] fun x : ℝ => x ^ (N + 1) := by
    have h := (isBigO_refl (fun x : ℝ => x ^ N) atTop).mul_isLittleO (isLittleO_log_pow_id M)
    refine h.congr' (Eventually.of_forall fun _ => rfl) ?_
    filter_upwards with x
    rw [pow_succ]
  exact hstep.trans (isLittleO_pow_exp_pos_mul_atTop (N + 1) hε)

end Fabius
