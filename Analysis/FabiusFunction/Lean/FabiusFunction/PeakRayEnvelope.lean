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

The mechanism is universal bookkeeping, isolated in
`decayGauge_dyadic_shell_identity`: for arbitrary positive shell constants
`A,D`, the rate

`Aᵏ/(2^{k(k+1)/2}(Dy)ᵏ)`

is exactly the dyadic ratio of the gauge with exponent
`1/2 + log(D/A)/log 2`.  The proof is a direct application of
`shell_exponent_identity`; it contains no special-function information.
Its specialization `gauge_ratio_identity` takes `A = √3/2`, `D = π`,
and `peak_ray_gauge_identity` then merely takes `y = 2/3`.
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

/-- For every real exponent `κ`, the decay gauge is strictly positive when `x > 0`. -/
theorem decayGauge_pos (κ : ℝ) {x : ℝ} (hx : 0 < x) : 0 < decayGauge κ x := by
  unfold decayGauge
  positivity

/-- **Universal dyadic shell-to-gauge identity.**  For arbitrary positive
shell numerator `A`, denominator scale `D`, and base point `y`, the exact
shell rate

`Aᵏ / (2^{k(k+1)/2} (Dy)ᵏ)`

is the ratio between the gauge of exponent
`1/2 + log(D/A)/log 2` at `2ᵏy` and at `y`.  This is the reusable algebraic
core of every dyadic decay exponent: the analytic input need only supply
the two positive constants `A` and `D`.

The shifted parameters `q = k - 1` and `b' = log 2 + log y` make this a
direct instance of `shell_exponent_identity`; its residual mantissa term is
exactly the negative logarithm of the gauge at `y`. -/
theorem decayGauge_dyadic_shell_identity
    (A D : ℝ) (hA : 0 < A) (hD : 0 < D) (k : ℕ) {y : ℝ} (hy : 0 < y) :
    A ^ k /
        ((2 : ℝ) ^ (k * (k + 1) / 2) * (D * y) ^ k) *
      decayGauge (1 / 2 + Real.log (D / A) / Real.log 2) y =
    decayGauge (1 / 2 + Real.log (D / A) / Real.log 2)
      ((2 : ℝ) ^ k * y) := by
  have hl2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 ≠ 0 := ne_of_gt hl2
  have hxk : (0 : ℝ) < (2 : ℝ) ^ k * y := by positivity
  have hlx : Real.log ((2 : ℝ) ^ k * y) =
      k * Real.log 2 + Real.log y := by
    rw [Real.log_mul (by positivity) (ne_of_gt hy), Real.log_pow]
  have hT : ((k * (k + 1) / 2 : ℕ) : ℝ) = (k : ℝ) * ((k : ℝ) + 1) / 2 := by
    have h2 : (k * (k + 1) / 2 : ℕ) * 2 = k * (k + 1) :=
      Nat.div_mul_cancel (Nat.even_mul_succ_self k).two_dvd
    have h3 := congrArg (fun m : ℕ => (m : ℝ)) h2
    push_cast at h3
    linarith
  have hlogDA : Real.log (D / A) = Real.log D - Real.log A :=
    Real.log_div (ne_of_gt hD) (ne_of_gt hA)
  have hlogDy : Real.log (D * y) = Real.log D + Real.log y :=
    Real.log_mul (ne_of_gt hD) (ne_of_gt hy)

  let a : ℝ := Real.log 2
  let b : ℝ := Real.log y
  let c : ℝ := Real.log (D / A)
  let L : ℝ := Real.log ((2 : ℝ) ^ k * y)
  let n : ℝ := k
  let q : ℝ := n - 1
  let b' : ℝ := a + b
  have hL : L = q * a + b' := by
    dsimp [L, q, b', n, a, b]
    rw [hlx]
    ring
  have hshell := shell_exponent_identity a b' c L q
    (by simpa only [a] using hl2') hL
  have hcorrection :
      b' ^ 2 / (2 * a) + b' * c / a - b' / 2 - c =
        b ^ 2 / (2 * a) + (1 / 2 + c / a) * b := by
    dsimp [b']
    ring
  have hbook :
      -(a / 2) * (n * (n + 1)) - n * (c + b) - b ^ 2 / (2 * a) +
          b * (-(1 / 2 + c / a)) =
        -(L ^ 2 / (2 * a)) + L * (-(1 / 2 + c / a)) := by
    calc
      -(a / 2) * (n * (n + 1)) - n * (c + b) - b ^ 2 / (2 * a) +
          b * (-(1 / 2 + c / a)) =
          (-(a / 2) * (q * (q + 1)) - (q + 1) * (c + b')) -
            b ^ 2 / (2 * a) + b * (-(1 / 2 + c / a)) := by
              dsimp [q, b']
              ring
      _ = (-(L ^ 2 / (2 * a)) - (1 / 2 + c / a) * L +
            (b' ^ 2 / (2 * a) + b' * c / a - b' / 2 - c)) -
            b ^ 2 / (2 * a) + b * (-(1 / 2 + c / a)) := by
              rw [hshell]
      _ = -(L ^ 2 / (2 * a)) + L * (-(1 / 2 + c / a)) := by
              rw [hcorrection]
              ring

  unfold decayGauge
  rw [Real.rpow_def_of_pos hy, Real.rpow_def_of_pos hxk]
  have e1 : A ^ k = Real.exp ((k : ℝ) * Real.log A) := by
    rw [Real.exp_nat_mul, Real.exp_log hA]
  have e2 : (2:ℝ) ^ (k * (k + 1) / 2) =
      Real.exp (((k * (k + 1) / 2 : ℕ) : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ) < 2)]
  have e3 : (D * y) ^ k = Real.exp ((k : ℝ) * Real.log (D * y)) := by
    rw [Real.exp_nat_mul, Real.exp_log (mul_pos hD hy)]
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
  dsimp [a, b, c, L, n] at hbook
  rw [hT, hlogDy, hlogDA]
  rw [hlogDA] at hbook
  convert hbook using 1 <;> ring

/-- **The gauge identity, at every positive base point**: the extremal
Fourier-shell rate is exactly the `E_{κ∞}` ratio between `y` and `2ᵏy`.
This is the specialization of `decayGauge_dyadic_shell_identity` to
`A = √3/2` and `D = π`. -/
theorem gauge_ratio_identity (k : ℕ) {y : ℝ} (hy : 0 < y) :
    (Real.sqrt 3 / 2) ^ k /
        ((2:ℝ) ^ (k * (k + 1) / 2) * (π * y) ^ k) *
      decayGauge kappaInf y =
    decayGauge kappaInf ((2:ℝ) ^ k * y) := by
  have hl2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hκ :
      1 / 2 + Real.log (π / (Real.sqrt 3 / 2)) / Real.log 2 = kappaInf := by
    unfold kappaInf
    rw [Real.log_div Real.pi_ne_zero (by positivity),
      Real.log_div Real.pi_ne_zero (by positivity),
      Real.log_div (by positivity) (by norm_num)]
    field_simp [hl2]
    ring
  simpa only [hκ] using
    decayGauge_dyadic_shell_identity (Real.sqrt 3 / 2) π
      (by positivity) Real.pi_pos k hy

/-- **The gauge identity of the peak ray**: the extremal shell rate of
the product form is exactly the `E_{κ∞}` gauge ratio along the ray,
`(√3/2)ᵏ/(2^{k(k+1)/2}(2π/3)ᵏ) · E_{κ∞}(2/3) = E_{κ∞}(2ᵏ·(2/3))`. -/
theorem peak_ray_gauge_identity (k : ℕ) :
    (Real.sqrt 3 / 2) ^ k /
        ((2:ℝ) ^ (k * (k + 1) / 2) * (2 * π / 3) ^ k) *
      decayGauge kappaInf (2 / 3 : ℝ) =
    decayGauge kappaInf ((2:ℝ) ^ k * (2 / 3)) := by
  have hπ : π * (2 / 3 : ℝ) = 2 * π / 3 := by ring
  simpa only [hπ] using
    gauge_ratio_identity k (by norm_num : (0 : ℝ) < 2 / 3)

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
