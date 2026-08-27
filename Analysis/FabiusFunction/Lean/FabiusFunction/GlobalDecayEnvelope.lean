import FabiusFunction.PeakRayEnvelope
import FabiusFunction.RvachevProductContinuity

/-!
# The global `κ∞` decay envelope

`PeakRayEnvelope` shows the exponent `κ∞` is *attained* along the ray
`2ᵏ·(2/3)`.  This file proves the matching upper bound on the whole
half-line: there is a constant `C` with

`‖Φ(x)‖ ≤ C · E_{κ∞}(x)`  for every `x ≥ 1`,

`E_κ(x) = exp(−log²x/(2 log 2))·x^{−κ}`.  Together the two say that
`κ∞` is exactly the envelope exponent of the Fourier decay: no larger
exponent holds, and this one holds globally.

Three ingredients: the gauge identity of the peak ray holds at *every*
base point (`gauge_ratio_identity` — the `y = 2/3` specialisation was
`peak_ray_gauge_identity`), the shell bound
`norm_rvachevFourierProduct_two_pow_mul_le` already holds along every
dyadic ray, and the ratio `‖Φ‖/E_{κ∞}` is continuous hence bounded on
the compact mantissa window `[1,2]`.

* `gauge_ratio_identity` — the gauge ratio at an arbitrary base point.
* `continuousOn_decayGauge` — continuity of the gauge.
* `exists_bound_on_mantissa_window` — the compact-window constant.
* `exists_dyadic_decomposition` — `x = 2ⁿ·y`, `y ∈ [1,2)`.
* `norm_rvachevFourierProduct_le_decayGauge` — **the envelope**.
-/

set_option autoImplicit false

open Finset Real Filter Topology

namespace Fabius

/-! ## The gauge ratio at an arbitrary base point -/

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

end Fabius
