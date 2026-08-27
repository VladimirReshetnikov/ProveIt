import FabiusFunction.SincProductPeakRay

/-!
# The `κ∞`-envelope form of the exact peak ray

`SincProductPeakRay` gives the exact peak ray in product form.  This
file converts it into the decay-audit's gauge form: with the extremal
exponent `κ∞ = 3/2 + log(π/√3)/log 2` and the log-normal–power gauge
`E_κ(x) = exp(−log²x/(2 log 2))·x^{−κ}`,

`‖Φ(2ᵏ·(2/3))‖ = C₊ · E_{κ∞}(2ᵏ·(2/3))` for every `k ≥ 0`,

with the constant `C₊ = ‖Φ(2/3)‖ / E_{κ∞}(2/3)` — Document 6's
`C₊ = W_{κ∞}(2/3) = 0.13912977473482934529…`, verified to 38 digits in
the second-wave audit and exact here.  The exponent `κ∞` is thereby
*attained* on an explicit geometric ray: the sharpest possible witness
that the envelope power of the Fourier-decay spectrum cannot be
improved.

The mechanism is bookkeeping, isolated in `peak_ray_gauge_identity`:
the extremal per-shell rate `(√3/2)ᵏ/(2^{k(k+1)/2}(2π/3)ᵏ)` of the
product form is *exactly* the gauge ratio `E_{κ∞}(2ᵏy)/E_{κ∞}(y)` at
`y = 2/3` — a single identity of exponentials, proved by reducing all
six factors to `exp` and closing a rational identity in the atoms
`log 2`, `log 3`, `log π`.
-/

set_option autoImplicit false

open Finset Real

namespace Fabius

/-- The extremal decay exponent of the Fourier-decay audit:
`κ∞ = 3/2 + log(π/√3)/log 2 = 2.3590148791117407…`. -/
noncomputable def kappaInf : ℝ := 3 / 2 + Real.log (π / Real.sqrt 3) / Real.log 2

/-- The log-normal–power gauge `E_κ(x) = exp(−log²x/(2 log 2))·x^{−κ}`
of the Fourier-decay audit. -/
noncomputable def decayGauge (κ x : ℝ) : ℝ :=
  Real.exp (-(Real.log x) ^ 2 / (2 * Real.log 2)) * x ^ (-κ)

theorem decayGauge_pos (κ : ℝ) {x : ℝ} (hx : 0 < x) : 0 < decayGauge κ x := by
  unfold decayGauge
  positivity

/-- **The gauge identity of the peak ray**: the extremal shell rate of
the product form is exactly the `E_{κ∞}` gauge ratio along the ray,
`(√3/2)ᵏ/(2^{k(k+1)/2}(2π/3)ᵏ) · E_{κ∞}(2/3) = E_{κ∞}(2ᵏ·(2/3))`. -/
theorem peak_ray_gauge_identity (k : ℕ) :
    (Real.sqrt 3 / 2) ^ k /
        ((2:ℝ) ^ (k * (k + 1) / 2) * (2 * π / 3) ^ k) *
      decayGauge kappaInf (2 / 3 : ℝ) =
    decayGauge kappaInf ((2:ℝ) ^ k * (2 / 3)) := by
  have hl2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 ≠ 0 := ne_of_gt hl2
  have h23 : (0:ℝ) < (2 / 3 : ℝ) := by norm_num
  have hxk : (0:ℝ) < (2:ℝ) ^ k * (2 / 3) := by positivity
  have hlx : Real.log ((2:ℝ) ^ k * (2 / 3)) =
      k * Real.log 2 + Real.log (2 / 3 : ℝ) := by
    rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  have hT : ((k * (k + 1) / 2 : ℕ) : ℝ) = (k : ℝ) * ((k : ℝ) + 1) / 2 := by
    have h2 : (k * (k + 1) / 2 : ℕ) * 2 = k * (k + 1) :=
      Nat.div_mul_cancel (Nat.even_mul_succ_self k).two_dvd
    have h3 := congrArg (fun m : ℕ => (m : ℝ)) h2
    push_cast at h3
    linarith
  have hls : Real.log (Real.sqrt 3 / 2) = Real.log 3 / 2 - Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num),
      Real.log_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  have hlc : Real.log (2 * π / 3) = Real.log 2 + Real.log π - Real.log 3 := by
    rw [Real.log_div (by positivity) (by norm_num),
      Real.log_mul (by norm_num) Real.pi_ne_zero]
  have hl23 : Real.log (2 / 3 : ℝ) = Real.log 2 - Real.log 3 :=
    Real.log_div (by norm_num) (by norm_num)
  have hlps : Real.log (π / Real.sqrt 3) = Real.log π - Real.log 3 / 2 := by
    rw [Real.log_div Real.pi_ne_zero (by positivity),
      Real.log_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  unfold decayGauge kappaInf
  rw [Real.rpow_def_of_pos h23, Real.rpow_def_of_pos hxk]
  have e1 : (Real.sqrt 3 / 2) ^ k =
      Real.exp ((k : ℝ) * Real.log (Real.sqrt 3 / 2)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  have e2 : (2:ℝ) ^ (k * (k + 1) / 2) =
      Real.exp (((k * (k + 1) / 2 : ℕ) : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ) < 2)]
  have e3 : (2 * π / 3 : ℝ) ^ k =
      Real.exp ((k : ℝ) * Real.log (2 * π / 3)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  rw [e1, e2, e3]
  have hcomb : ∀ A B C D E : ℝ,
      Real.exp A / (Real.exp B * Real.exp C) * (Real.exp D * Real.exp E) =
        Real.exp (A - B - C + D + E) := by
    intro A B C D E
    rw [← Real.exp_add B C, ← Real.exp_add D E, div_mul_eq_mul_div,
      ← Real.exp_add, ← Real.exp_sub]
    congr 1
    ring
  rw [hcomb, ← Real.exp_add, Real.exp_eq_exp]
  rw [hlx, hT, hls, hlc, hl23, hlps]
  field_simp
  ring

/-- **The exact peak ray in envelope form** (Document 6 of the second
wave, exact): with `C₊ = ‖Φ(2/3)‖ / E_{κ∞}(2/3)`,
`‖Φ(2ᵏ·(2/3))‖ = C₊·E_{κ∞}(2ᵏ·(2/3))` for every `k` — the extremal
exponent `κ∞` is attained, with a constant, on an explicit geometric
ray. -/
theorem norm_rvachevFourierProduct_peak_ray_envelope (k : ℕ) :
    ‖rvachevFourierProduct ((2:ℂ) ^ k * ((2 / 3 : ℝ) : ℂ))‖ =
      (‖rvachevFourierProduct (((2 / 3 : ℝ) : ℂ))‖ /
          decayGauge kappaInf (2 / 3 : ℝ)) *
        decayGauge kappaInf ((2:ℝ) ^ k * (2 / 3)) := by
  have hE : decayGauge kappaInf (2 / 3 : ℝ) ≠ 0 :=
    ne_of_gt (decayGauge_pos _ (by norm_num))
  rw [norm_rvachevFourierProduct_two_pow_two_thirds k, ← peak_ray_gauge_identity k]
  field_simp

end Fabius
