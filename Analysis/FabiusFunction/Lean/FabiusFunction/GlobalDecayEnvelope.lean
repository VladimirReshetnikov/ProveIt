import FabiusFunction.PeakRayEnvelope
import FabiusFunction.RvachevProductContinuity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The global `κ∞` decay envelope

`PeakRayEnvelope` shows the exponent `κ∞` is *attained* along the ray
`2ᵏ·(2/3)`.  This file proves the matching upper bound on the positive
half-line: there is a constant `C` with

`‖Φ(x)‖ ≤ C · E_{κ∞}(x)`  for every `x ≥ 1`,

`E_κ(x) = exp(−log²x/(2 log 2))·x^{−κ}`.  Evenness then gives the
two-sided real-axis form

`‖Φ(x)‖ ≤ C · E_{κ∞}(|x|)`  whenever `|x| ≥ 1`.

Thus the global upper envelope uses the same `κ∞` gauge that the
distinguished dyadic peak ray attains exactly.  This exponent is sharp:
if `κ > κ∞`, then along that same ray

`‖Φ(2ᵏ·(2/3))‖ / E_κ(2ᵏ·(2/3)) → +∞`.

Consequently no constant can give a global `E_κ` envelope when
`κ > κ∞`; an explicit point of the form `2ᵏ·(2/3) ≥ 1`
violates any proposed bound.

The upper bound has three ingredients: the gauge identity of the peak ray holds at *every*
base point (`gauge_ratio_identity` — the `y = 2/3` specialisation was
`peak_ray_gauge_identity`), the shell bound
`norm_rvachevFourierProduct_two_pow_mul_le` already holds along every
dyadic ray, and the ratio `‖Φ‖/E_{κ∞}` is continuous hence bounded on
the compact mantissa window `[1,2]`.

* `gauge_ratio_identity` — the gauge ratio at an arbitrary base point.
* `decayGauge_div_decayGauge` — comparison of two gauges at a positive point.
* `continuousOn_decayGauge` — continuity of the gauge.
* `exists_bound_on_mantissa_window` — the compact-window constant.
* `exists_dyadic_decomposition` — `x = 2ⁿ·y`, `y ∈ [1,2)`.
* `norm_rvachevFourierProduct_le_decayGauge` — the positive-ray envelope.
* `norm_rvachevFourierProduct_le_decayGauge_abs` — **the two-sided
  real-axis envelope**.
* `norm_rvachevFourierProduct_peak_ray_ratio_tendsto_atTop` — every
  stronger exponent diverges after normalization on the peak ray.
* `exists_peak_ray_norm_gt_mul_decayGauge` — an explicit peak-ray
  obstruction to every proposed stronger envelope.
* `not_exists_norm_rvachevFourierProduct_le_decayGauge_of_kappaInf_lt`
  — the global sharpness statement.
-/

set_option autoImplicit false

open Finset Real Filter Topology

namespace Fabius

/-! ## The gauge ratio at an arbitrary base point -/

/-- At a positive point the quotient of two decay gauges is just the
corresponding power correction:
`E_{κ₁}(x) / E_{κ₂}(x) = x ^ (κ₂ - κ₁)`.

The log-normal factors cancel completely; this identity is the bridge
from exact `κ∞`-attainment to sharpness among all gauge exponents. -/
theorem decayGauge_div_decayGauge (κ₁ κ₂ : ℝ) {x : ℝ} (hx : 0 < x) :
    decayGauge κ₁ x / decayGauge κ₂ x = x ^ (κ₂ - κ₁) := by
  unfold decayGauge
  rw [mul_div_mul_left _ _ (Real.exp_ne_zero _), ← Real.rpow_sub hx]
  congr 1
  ring

/-- **The gauge identity, at every base point**: the extremal shell
rate is exactly the `E_{κ∞}` ratio between `y` and `2ᵏy`, for every
`y > 0`.  (At `y = 2/3` this is `peak_ray_gauge_identity`; the general
statement is no harder, since `log y` simply stays an atom.) -/
theorem gauge_ratio_identity (k : ℕ) {y : ℝ} (hy : 0 < y) :
    (Real.sqrt 3 / 2) ^ k /
        ((2:ℝ) ^ (k * (k + 1) / 2) * (π * y) ^ k) *
      decayGauge kappaInf y =
    decayGauge kappaInf ((2:ℝ) ^ k * y) := by
  have hl2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 ≠ 0 := ne_of_gt hl2
  have hxk : (0:ℝ) < (2:ℝ) ^ k * y := by positivity
  have hlx : Real.log ((2:ℝ) ^ k * y) =
      k * Real.log 2 + Real.log y := by
    rw [Real.log_mul (by positivity) (ne_of_gt hy), Real.log_pow]
  have hT : ((k * (k + 1) / 2 : ℕ) : ℝ) = (k : ℝ) * ((k : ℝ) + 1) / 2 := by
    have h2 : (k * (k + 1) / 2 : ℕ) * 2 = k * (k + 1) :=
      Nat.div_mul_cancel (Nat.even_mul_succ_self k).two_dvd
    have h3 := congrArg (fun m : ℕ => (m : ℝ)) h2
    push_cast at h3
    linarith
  have hls : Real.log (Real.sqrt 3 / 2) = Real.log 3 / 2 - Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num),
      Real.log_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  have hlc : Real.log (π * y) = Real.log π + Real.log y :=
    Real.log_mul Real.pi_ne_zero (ne_of_gt hy)
  have hlps : Real.log (π / Real.sqrt 3) =
      Real.log π - Real.log 3 / 2 := by
    rw [Real.log_div Real.pi_ne_zero (by positivity),
      Real.log_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  unfold decayGauge kappaInf
  rw [Real.rpow_def_of_pos hy, Real.rpow_def_of_pos hxk]
  have e1 : (Real.sqrt 3 / 2) ^ k =
      Real.exp ((k : ℝ) * Real.log (Real.sqrt 3 / 2)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  have e2 : (2:ℝ) ^ (k * (k + 1) / 2) =
      Real.exp (((k * (k + 1) / 2 : ℕ) : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ) < 2)]
  have e3 : (π * y) ^ k = Real.exp ((k : ℝ) * Real.log (π * y)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  rw [e1, e2, e3]
  have hcomb : ∀ A B C D E : ℝ,
      Real.exp A / (Real.exp B * Real.exp C) *
          (Real.exp D * Real.exp E) =
        Real.exp (A - B - C + D + E) := by
    intro A B C D E
    rw [← Real.exp_add B C, ← Real.exp_add D E, div_mul_eq_mul_div,
      ← Real.exp_add, ← Real.exp_sub]
    congr 1
    ring
  rw [hcomb, ← Real.exp_add, Real.exp_eq_exp]
  rw [hlx, hT, hls, hlc, hlps]
  field_simp
  ring

/-! ## Continuity of the gauge -/

/-- For every exponent `κ`, the decay gauge `E_κ` is continuous on the
positive half-line. -/
theorem continuousOn_decayGauge (κ : ℝ) :
    ContinuousOn (decayGauge κ) (Set.Ioi 0) := by
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  apply ContinuousAt.continuousWithinAt
  unfold decayGauge
  have hinner : ContinuousAt
      (fun t : ℝ => -(Real.log t) ^ 2 / (2 * Real.log 2)) x :=
    ((Real.continuousAt_log hx0).pow 2).neg.div_const _
  have h1 : ContinuousAt
      (fun t : ℝ => Real.exp (-(Real.log t) ^ 2 / (2 * Real.log 2))) x := by
    simpa [Function.comp_def] using
      Real.continuous_exp.continuousAt.comp hinner
  have h2 : ContinuousAt (fun t : ℝ => t ^ (-κ)) x :=
    Real.continuousAt_rpow_const x (-κ) (Or.inl hx0)
  exact h1.mul h2

/-! ## The compact mantissa window -/

/-- No lattice point sits at a half-integer, so `Φ(3/2) ≠ 0`. -/
theorem norm_rvachevFourierProduct_three_halves_pos :
    0 < ‖rvachevFourierProduct ((3/2 : ℝ) : ℂ)‖ := by
  apply norm_rvachevFourierProduct_pos_of_ne
  intro p hp
  rw [abs_of_pos (by norm_num : (0:ℝ) < 3/2)] at hp
  have hnat : ((2 ^ p.1 * (p.2 + 1) : ℕ) : ℝ) = 3/2 := hp
  have h2 : ((2 * (2 ^ p.1 * (p.2 + 1)) : ℕ) : ℝ) = 3 := by
    push_cast
    push_cast at hnat
    linarith
  have h3 : 2 * (2 ^ p.1 * (p.2 + 1)) = 3 := by exact_mod_cast h2
  omega

/-- **The compact-window constant**: on the mantissa window `[1,2]`
the modulus is dominated by the gauge, with a positive constant. -/
theorem exists_bound_on_mantissa_window :
    ∃ M : ℝ, 0 < M ∧ ∀ y ∈ Set.Icc (1:ℝ) 2,
      ‖rvachevFourierProduct (y : ℂ)‖ ≤ M * decayGauge kappaInf y := by
  have hsub : Set.Icc (1:ℝ) 2 ⊆ Set.Ioi 0 := fun y hy =>
    lt_of_lt_of_le zero_lt_one hy.1
  have hgpos : ∀ y ∈ Set.Icc (1:ℝ) 2, 0 < decayGauge kappaInf y :=
    fun y hy => decayGauge_pos _ (hsub hy)
  have hcont : ContinuousOn
      (fun y : ℝ => ‖rvachevFourierProduct (y : ℂ)‖ /
        decayGauge kappaInf y) (Set.Icc 1 2) := by
    apply ContinuousOn.div
    · exact continuous_norm_rvachevFourierProduct.continuousOn
    · exact (continuousOn_decayGauge kappaInf).mono hsub
    · exact fun y hy => ne_of_gt (hgpos y hy)
  obtain ⟨y₀, hy₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by norm_num)) hcont
  refine ⟨‖rvachevFourierProduct ((y₀ : ℝ) : ℂ)‖ /
    decayGauge kappaInf y₀, ?_, ?_⟩
  · -- positivity: the maximum dominates the value at `3/2`
    have hmem : (3/2 : ℝ) ∈ Set.Icc (1:ℝ) 2 := by
      constructor <;> norm_num
    have hle := hmax hmem
    have hpos : 0 < ‖rvachevFourierProduct ((3/2 : ℝ) : ℂ)‖ /
        decayGauge kappaInf (3/2) :=
      div_pos norm_rvachevFourierProduct_three_halves_pos
        (hgpos _ hmem)
    exact lt_of_lt_of_le hpos hle
  · intro y hy
    have hle : ‖rvachevFourierProduct (y : ℂ)‖ / decayGauge kappaInf y ≤
        ‖rvachevFourierProduct ((y₀ : ℝ) : ℂ)‖ /
          decayGauge kappaInf y₀ := hmax hy
    rwa [div_le_iff₀ (hgpos y hy)] at hle

/-! ## Dyadic decomposition of the half-line -/

/-- Every `x ≥ 1` sits in exactly one dyadic block `[2ⁿ, 2ⁿ⁺¹)`. -/
theorem exists_pow_two_le_lt {x : ℝ} (hx : 1 ≤ x) :
    ∃ n : ℕ, (2:ℝ) ^ n ≤ x ∧ x < 2 ^ (n + 1) := by
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hl2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have ht0 : 0 ≤ Real.log x / Real.log 2 :=
    div_nonneg (Real.log_nonneg hx) hl2.le
  refine ⟨⌊Real.log x / Real.log 2⌋₊, ?_, ?_⟩
  · have hnt : ((⌊Real.log x / Real.log 2⌋₊ : ℕ) : ℝ) ≤
        Real.log x / Real.log 2 := Nat.floor_le ht0
    rw [le_div_iff₀ hl2] at hnt
    have h2 : Real.log ((2:ℝ) ^ (⌊Real.log x / Real.log 2⌋₊ : ℕ)) ≤
        Real.log x := by
      rwa [Real.log_pow]
    have h3 := Real.exp_le_exp.mpr h2
    rwa [Real.exp_log (by positivity), Real.exp_log hx0] at h3
  · have htn : Real.log x / Real.log 2 <
        ((⌊Real.log x / Real.log 2⌋₊ : ℕ) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    rw [div_lt_iff₀ hl2] at htn
    have h2 : Real.log x <
        Real.log ((2:ℝ) ^ ((⌊Real.log x / Real.log 2⌋₊ : ℕ) + 1)) := by
      rw [Real.log_pow]
      push_cast
      linarith
    have h3 := Real.exp_lt_exp.mpr h2
    rwa [Real.exp_log hx0, Real.exp_log (by positivity)] at h3

/-- Every `x ≥ 1` is `2ⁿ` times a mantissa in `[1,2)`. -/
theorem exists_dyadic_decomposition {x : ℝ} (hx : 1 ≤ x) :
    ∃ (n : ℕ) (y : ℝ), y ∈ Set.Ico (1:ℝ) 2 ∧ x = 2 ^ n * y := by
  obtain ⟨n, hlow, hhigh⟩ := exists_pow_two_le_lt hx
  have hpow : (0:ℝ) < (2:ℝ) ^ n := by positivity
  refine ⟨n, x / 2 ^ n, ⟨?_, ?_⟩, ?_⟩
  · rw [le_div_iff₀ hpow]
    linarith
  · rw [div_lt_iff₀ hpow]
    have : (2:ℝ) ^ (n + 1) = 2 ^ n * 2 := by rw [pow_succ]
    linarith [hhigh, this]
  · field_simp

/-! ## The envelope -/

/-- **The global `κ∞` envelope**: `‖Φ(x)‖ ≤ C·E_{κ∞}(x)` for all
`x ≥ 1`.  With `PeakRayEnvelope`'s attainment along `2ᵏ·(2/3)`, this
pins `κ∞` as exactly the envelope exponent of the Fourier decay. -/
theorem norm_rvachevFourierProduct_le_decayGauge :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
      ‖rvachevFourierProduct (x : ℂ)‖ ≤ C * decayGauge kappaInf x := by
  obtain ⟨M, hM, hwin⟩ := exists_bound_on_mantissa_window
  refine ⟨Real.sqrt (5/3) * M, by positivity, ?_⟩
  intro x hx
  obtain ⟨n, y, hy, rfl⟩ := exists_dyadic_decomposition hx
  have hy0 : (0:ℝ) < y := lt_of_lt_of_le zero_lt_one hy.1
  have hyIcc : y ∈ Set.Icc (1:ℝ) 2 := ⟨hy.1, hy.2.le⟩
  have hcast : (((2:ℝ) ^ n * y : ℝ) : ℂ) = (2:ℂ) ^ n * (y : ℂ) := by
    push_cast
    ring
  rw [hcast]
  -- the shell bound along the ray through `y`
  have hshell := norm_rvachevFourierProduct_two_pow_mul_le n y (ne_of_gt hy0)
  rw [abs_of_pos hy0] at hshell
  set R : ℝ := (Real.sqrt 3 / 2) ^ n /
    ((2:ℝ) ^ (n * (n + 1) / 2) * (π * y) ^ n) with hR
  have hR0 : 0 < R := by
    have : (0:ℝ) < (2:ℝ) ^ (n * (n + 1) / 2) * (π * y) ^ n := by
      have := Real.pi_pos
      positivity
    rw [hR]
    positivity
  have hshell' : ‖rvachevFourierProduct ((2:ℂ) ^ n * (y : ℂ))‖ ≤
      Real.sqrt (5/3) * R * ‖rvachevFourierProduct (y : ℂ)‖ := by
    rw [hR]
    calc ‖rvachevFourierProduct ((2:ℂ) ^ n * (y : ℂ))‖ ≤
        Real.sqrt (5 / 3) * (Real.sqrt 3 / 2) ^ n /
          ((2:ℝ) ^ (n * (n + 1) / 2) * (π * y) ^ n) *
          ‖rvachevFourierProduct (y : ℂ)‖ := hshell
      _ = Real.sqrt (5/3) * ((Real.sqrt 3 / 2) ^ n /
          ((2:ℝ) ^ (n * (n + 1) / 2) * (π * y) ^ n)) *
          ‖rvachevFourierProduct (y : ℂ)‖ := by ring
  -- window bound, then the gauge identity
  have hwin' := hwin y hyIcc
  have hchain : Real.sqrt (5/3) * R *
      ‖rvachevFourierProduct (y : ℂ)‖ ≤
      Real.sqrt (5/3) * R * (M * decayGauge kappaInf y) := by
    apply mul_le_mul_of_nonneg_left hwin'
    have : (0:ℝ) ≤ Real.sqrt (5/3) := Real.sqrt_nonneg _
    positivity
  have hid : R * decayGauge kappaInf y =
      decayGauge kappaInf ((2:ℝ) ^ n * y) := by
    rw [hR]
    exact gauge_ratio_identity n hy0
  calc ‖rvachevFourierProduct ((2:ℂ) ^ n * (y : ℂ))‖ ≤
      Real.sqrt (5/3) * R * ‖rvachevFourierProduct (y : ℂ)‖ := hshell'
    _ ≤ Real.sqrt (5/3) * R * (M * decayGauge kappaInf y) := hchain
    _ = Real.sqrt (5/3) * M * (R * decayGauge kappaInf y) := by ring
    _ = Real.sqrt (5/3) * M * decayGauge kappaInf ((2:ℝ) ^ n * y) := by
        rw [hid]

/-- **The two-sided global `κ∞` envelope**: one positive constant controls
the Fourier modulus on both real tails,
`‖Φ(x)‖ ≤ C · E_{κ∞}(|x|)` whenever `1 ≤ |x|`.

This is the natural whole-real-axis form of
`norm_rvachevFourierProduct_le_decayGauge`: apply the positive-frequency
bound at `|x|`, then use evenness of the sinc product on the negative tail. -/
theorem norm_rvachevFourierProduct_le_decayGauge_abs :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ |x| →
      ‖rvachevFourierProduct (x : ℂ)‖ ≤ C * decayGauge kappaInf |x| := by
  obtain ⟨C, hC, hbound⟩ := norm_rvachevFourierProduct_le_decayGauge
  refine ⟨C, hC, ?_⟩
  intro x hx
  have h := hbound |x| hx
  by_cases hx0 : 0 ≤ x
  · simpa only [abs_of_nonneg hx0] using h
  · have hxnonpos : x ≤ 0 := (lt_of_not_ge hx0).le
    simpa only [abs_of_nonpos hxnonpos,
      norm_rvachevFourierProduct_neg] using h

/-! ## Sharpness of the exponent -/

/-- **Every stronger gauge exponent diverges on the exact peak ray.**
If `κ > κ∞`, then

`‖Φ(2ᵏ·(2/3))‖ / E_κ(2ᵏ·(2/3)) → +∞`.

Indeed the exact `κ∞` peak-ray identity leaves a fixed positive
coefficient, while `decayGauge_div_decayGauge` turns the remaining
quotient into `(2ᵏ·(2/3)) ^ (κ - κ∞)`. -/
theorem norm_rvachevFourierProduct_peak_ray_ratio_tendsto_atTop
    {κ : ℝ} (hκ : kappaInf < κ) :
    Tendsto
      (fun k : ℕ =>
        ‖rvachevFourierProduct
            ((((2 : ℝ) ^ k * (2 / 3 : ℝ) : ℝ) : ℂ))‖ /
          decayGauge κ ((2 : ℝ) ^ k * (2 / 3 : ℝ)))
      atTop atTop := by
  have hbase :
      0 < ‖rvachevFourierProduct (((2 / 3 : ℝ) : ℂ))‖ :=
    norm_rvachevFourierProduct_pos (by norm_num)
  have hcoefficient :
      0 < ‖rvachevFourierProduct (((2 / 3 : ℝ) : ℂ))‖ /
        decayGauge kappaInf (2 / 3 : ℝ) :=
    div_pos hbase (decayGauge_pos _ (by norm_num))
  have hray :
      Tendsto (fun k : ℕ => (2 : ℝ) ^ k * (2 / 3 : ℝ))
        atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const
      (by norm_num)
  have hpower :
      Tendsto
        (fun k : ℕ =>
          ((2 : ℝ) ^ k * (2 / 3 : ℝ)) ^ (κ - kappaInf))
        atTop atTop := by
    simpa only [Function.comp_def] using
      (tendsto_rpow_atTop (sub_pos.mpr hκ)).comp hray
  have hscaled :
      Tendsto
        (fun k : ℕ =>
          (‖rvachevFourierProduct (((2 / 3 : ℝ) : ℂ))‖ /
              decayGauge kappaInf (2 / 3 : ℝ)) *
            ((2 : ℝ) ^ k * (2 / 3 : ℝ)) ^ (κ - kappaInf))
        atTop atTop :=
    hpower.const_mul_atTop hcoefficient
  refine hscaled.congr' (Filter.Eventually.of_forall fun k => ?_)
  have hxk : 0 < (2 : ℝ) ^ k * (2 / 3 : ℝ) := by positivity
  have hcast :
      ((((2 : ℝ) ^ k * (2 / 3 : ℝ) : ℝ) : ℂ)) =
        (2 : ℂ) ^ k * ((2 / 3 : ℝ) : ℂ) := by
    push_cast
    ring
  symm
  dsimp only
  rw [hcast, norm_rvachevFourierProduct_peak_ray_envelope,
    mul_div_assoc, decayGauge_div_decayGauge _ _ hxk]

/-- **Explicit failure of every stronger global envelope.**  If
`κ > κ∞`, then for every proposed constant `C` there is a dyadic
peak-ray point `x = 2ᵏ·(2/3) ≥ 1` at which
`C · E_κ(x) < ‖Φ(x)‖`.

The conclusion is stated for arbitrary real `C`, slightly strengthening
the positive-constant form needed to refute a decay envelope. -/
theorem exists_peak_ray_norm_gt_mul_decayGauge
    {κ : ℝ} (hκ : kappaInf < κ) (C : ℝ) :
    ∃ k : ℕ,
      1 ≤ (2 : ℝ) ^ k * (2 / 3 : ℝ) ∧
        C * decayGauge κ ((2 : ℝ) ^ k * (2 / 3 : ℝ)) <
          ‖rvachevFourierProduct
            ((((2 : ℝ) ^ k * (2 / 3 : ℝ) : ℝ) : ℂ))‖ := by
  obtain ⟨k, hk, hratio⟩ :=
    ((eventually_ge_atTop (1 : ℕ)).and
      ((norm_rvachevFourierProduct_peak_ray_ratio_tendsto_atTop hκ).eventually_gt_atTop
        C)).exists
  refine ⟨k, ?_, ?_⟩
  · have hpow : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ k :=
      pow_le_pow_right₀ (by norm_num) hk
    calc
      1 ≤ (2 : ℝ) ^ 1 * (2 / 3 : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ k * (2 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_right hpow (by norm_num)
  · exact (lt_div_iff₀ (decayGauge_pos κ (by positivity))).mp hratio

/-- No positive constant gives a global `E_κ` envelope on `x ≥ 1`
when `κ > κ∞`.  Together with
`norm_rvachevFourierProduct_le_decayGauge`, this makes `κ∞` the
sharp exponent in this family of global decay gauges. -/
theorem not_exists_norm_rvachevFourierProduct_le_decayGauge_of_kappaInf_lt
    {κ : ℝ} (hκ : kappaInf < κ) :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
      ‖rvachevFourierProduct (x : ℂ)‖ ≤ C * decayGauge κ x := by
  rintro ⟨C, hC, hbound⟩
  obtain ⟨k, hx, hstrict⟩ := exists_peak_ray_norm_gt_mul_decayGauge hκ C
  exact (not_lt_of_ge (hbound _ hx)) hstrict

end Fabius
