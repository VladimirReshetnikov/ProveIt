import FabiusFunction.DirichletKernelCotangent
import FabiusFunction.CocycleCovarianceHalving
import FabiusFunction.DyadicCombTrapezoid
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The log-sine Fourier coefficients: `∫₀¹ log (2 sin πt) cos (2πmt) dt = −1/(2m)`

The analytic centerpiece of the audits' Clausen layer.  Integration by
parts on `[ε, 1−ε]` against `(log 2 sin πt)' = π·cot πt` turns the
Fourier pairing into the cotangent pairing of
`DirichletKernelCotangent`; the boundary terms vanish like `ε log ε`,
and the primitive-continuity of interval integrals passes to the limit
`ε → 0⁺`:

`∫₀¹ log (2 sin πt)·cos (2(m)πt) dt = −1/(2m)`  (`m = n+1 ≥ 1`).

With Parseval and Basel (`ζ(2) = π²/6`), these coefficients give the
Clausen values `∫₀¹ ψ² = π²/12` and `∫₀¹ d² = π²/4` of the variance
theorem — the remaining numerical inputs of Document 6.

* `eps_mul_abs_log_le_sqrt` — `ε·|log ε| ≤ 7√ε` on `(0,1]`.
* `abs_log_two_sin_le` — `|log (2 sin πε)| ≤ |log ε| + 2` on `(0,½]`.
* `intervalIntegrable_log_two_sin_mul_cos` — integrability of the
  pairing.
* `integral_log_two_sin_mul_cos` — **the Fourier coefficient**.
-/

set_option autoImplicit false

open Filter Topology intervalIntegral Real MeasureTheory

namespace Fabius

/-- Quantitative boundary bound: `ε·|log ε| ≤ 7·√ε` on `(0,1]`
(squaring reduces it to the barrier of `SquareLogIntegrable`). -/
theorem eps_mul_abs_log_le_sqrt {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1) :
    ε * |Real.log ε| ≤ 7 * Real.sqrt ε := by
  have hsq := sq_log_le_rpow h0 h1
  have key : (ε * |Real.log ε|) ^ 2 ≤ 49 * ε := by
    have h2 : (ε * |Real.log ε|) ^ 2 = ε ^ 2 * Real.log ε ^ 2 := by
      rw [mul_pow, sq_abs]
    have h3 : ε ^ 2 * Real.log ε ^ 2 ≤ ε ^ 2 * (48 * ε ^ (-(1 / 2) : ℝ)) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have h4 : ε ^ 2 * (48 * ε ^ (-(1 / 2) : ℝ)) =
        48 * (ε ^ ((2 : ℝ)) * ε ^ (-(1 / 2) : ℝ)) := by
      rw [show ε ^ ((2 : ℝ)) = ε ^ (2 : ℕ) by
        rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]]
      ring
    have h5 : ε ^ ((2 : ℝ)) * ε ^ (-(1 / 2) : ℝ) = ε ^ ((3 : ℝ) / 2) := by
      rw [← Real.rpow_add h0]
      norm_num
    have h6 : ε ^ ((3 : ℝ) / 2) ≤ ε ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge h0 h1 (by norm_num)
    have h7 : ε ^ (1 : ℝ) = ε := Real.rpow_one ε
    calc (ε * |Real.log ε|) ^ 2 = ε ^ 2 * Real.log ε ^ 2 := h2
      _ ≤ ε ^ 2 * (48 * ε ^ (-(1 / 2) : ℝ)) := h3
      _ = 48 * (ε ^ ((2 : ℝ)) * ε ^ (-(1 / 2) : ℝ)) := h4
      _ = 48 * ε ^ ((3 : ℝ) / 2) := by rw [h5]
      _ ≤ 48 * ε ^ (1 : ℝ) :=
          mul_le_mul_of_nonneg_left h6 (by norm_num)
      _ = 48 * ε := by rw [h7]
      _ ≤ 49 * ε := by linarith
  have h8 : 0 ≤ ε * |Real.log ε| := by positivity
  calc ε * |Real.log ε| = Real.sqrt ((ε * |Real.log ε|) ^ 2) :=
        (Real.sqrt_sq h8).symm
    _ ≤ Real.sqrt (49 * ε) := Real.sqrt_le_sqrt key
    _ = 7 * Real.sqrt ε := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 49),
          show (49 : ℝ) = 7 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 7)]

/-- On `(0, 1/2]` the cocycle value is within `2` of `log ε`:
`|log (2 sin πε)| ≤ |log ε| + 2` (Jordan bracket + `2π < e²`). -/
theorem abs_log_two_sin_le {ε : ℝ} (h0 : 0 < ε) (h2 : ε ≤ 1 / 2) :
    |Real.log (2 * Real.sin (π * ε))| ≤ |Real.log ε| + 2 := by
  have hπ := Real.pi_pos
  have hlow : 2 * ε ≤ Real.sin (π * ε) := by
    have h := Real.mul_le_sin (x := π * ε) (by positivity) (by nlinarith)
    calc 2 * ε = 2 / π * (π * ε) := by field_simp
      _ ≤ Real.sin (π * ε) := h
  have hup : Real.sin (π * ε) ≤ π * ε := (Real.sin_lt (by positivity)).le
  have hL : Real.log (4 * ε) ≤ Real.log (2 * Real.sin (π * ε)) := by
    apply Real.log_le_log (by positivity)
    nlinarith
  have hU : Real.log (2 * Real.sin (π * ε)) ≤ Real.log (2 * π * ε) := by
    apply Real.log_le_log (by nlinarith : (0:ℝ) < 2 * Real.sin (π * ε))
    nlinarith
  have hL' : Real.log (4 * ε) = Real.log 4 + Real.log ε :=
    Real.log_mul (by norm_num) (ne_of_gt h0)
  have hU' : Real.log (2 * π * ε) = Real.log (2 * π) + Real.log ε :=
    Real.log_mul (by positivity) (ne_of_gt h0)
  have h4 : Real.log 4 ≤ 2 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    have he : (2:ℝ) ≤ Real.exp 1 := by linarith
    have : (4:ℝ) ≤ Real.exp 2 := by
      have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]
        norm_num
      nlinarith
    calc Real.log 4 ≤ Real.log (Real.exp 2) :=
          Real.log_le_log (by norm_num) this
      _ = 2 := Real.log_exp 2
  have h2π : Real.log (2 * π) ≤ 2 := by
    have hpi : π < 3.15 := Real.pi_lt_d2
    have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    have : (2 * π : ℝ) ≤ Real.exp 2 := by nlinarith
    calc Real.log (2 * π) ≤ Real.log (Real.exp 2) :=
          Real.log_le_log (by positivity) this
      _ = 2 := Real.log_exp 2
  have hlogε : Real.log ε ≤ 0 := Real.log_nonpos h0.le (by linarith)
  have h40 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have h2π0 : 0 < Real.log (2 * π) := Real.log_pos (by nlinarith)
  rw [abs_le]
  have hL2 : Real.log 4 + Real.log ε ≤ Real.log (2 * Real.sin (π * ε)) := by
    rw [← hL']
    exact hL
  have hU2 : Real.log (2 * Real.sin (π * ε)) ≤
      Real.log (2 * π) + Real.log ε := by
    rw [← hU']
    exact hU
  constructor
  · have := neg_abs_le (Real.log ε)
    linarith
  · have := le_abs_self (Real.log ε)
    linarith

/-- The Fourier pairing `log (2 sin πt)·cos (2(n+1)πt)` is interval
integrable on `[0,1]`. -/
theorem intervalIntegrable_log_two_sin_mul_cos (n : ℕ) :
    IntervalIntegrable (fun t => Real.log (2 * Real.sin (π * t)) *
      Real.cos (2 * (n + 1) * (π * t))) MeasureTheory.volume 0 1 := by
  have hdom : IntervalIntegrable
      (fun t => (1 + Real.log (2 * Real.sin (π * t)) ^ 2) / 2)
      MeasureTheory.volume 0 1 :=
    (intervalIntegrable_const.add
      intervalIntegrable_sq_log_two_sin_pi_mul).div_const 2
  apply hdom.mono_fun
  · exact (measurable_log_two_sin_pi_mul.mul
      (Continuous.measurable (by fun_prop))).aestronglyMeasurable
  · filter_upwards with t
    set A := Real.log (2 * Real.sin (π * t))
    simp only [Real.norm_eq_abs]
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 + A ^ 2) / 2)]
    have hcos : |Real.cos (2 * (n + 1) * (π * t))| ≤ 1 :=
      Real.abs_cos_le_one _
    have hA : |A| ≤ (1 + A ^ 2) / 2 := by
      nlinarith [sq_nonneg (|A| - 1), sq_abs A, abs_nonneg A]
    calc |A| * |Real.cos (2 * (n + 1) * (π * t))| ≤ |A| * 1 :=
          mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
      _ = |A| := mul_one _
      _ ≤ (1 + A ^ 2) / 2 := hA

/-- **The log-sine Fourier coefficient**:

`∫₀¹ log (2 sin πt)·cos (2(n+1)·πt) dt = −1/(2(n+1))`.

Integration by parts on `[ε, 1−ε]` against `π cot πt`, the Dirichlet
cotangent pairing, boundary decay `ε log ε → 0`, and primitive
continuity in the limit `ε → 0⁺`. -/
theorem integral_log_two_sin_mul_cos (n : ℕ) :
    ∫ t in (0:ℝ)..1, Real.log (2 * Real.sin (π * t)) *
      Real.cos (2 * (n + 1) * (π * t)) = -(1 / (2 * (n + 1))) := by
  set m : ℝ := (n : ℝ) + 1 with hm
  have hm0 : 0 < m := by positivity
  have hc0 : (2 * m * π) ≠ 0 := by positivity
  -- the four functions of the integration by parts
  set u : ℝ → ℝ := fun t => Real.log (2 * Real.sin (π * t)) with hu_def
  set v : ℝ → ℝ := fun t => Real.sin (2 * m * (π * t)) / (2 * m * π)
    with hv_def
  set u' : ℝ → ℝ := fun t => π * (Real.cos (π * t) / Real.sin (π * t))
    with hu'_def
  set v' : ℝ → ℝ := fun t => Real.cos (2 * m * (π * t)) with hv'_def
  -- global integrability of u·v'
  have hint_uv : IntervalIntegrable (fun t => u t * v' t)
      MeasureTheory.volume 0 1 := intervalIntegrable_log_two_sin_mul_cos n
  -- derivative facts
  have hv_deriv : ∀ x : ℝ, HasDerivAt v (v' x) x := by
    intro x
    have hg : HasDerivAt (fun t : ℝ => 2 * m * (π * t)) (2 * m * π) x := by
      have h1 : HasDerivAt (fun t : ℝ => π * t) π x := by
        simpa using (hasDerivAt_id x).const_mul π
      simpa [mul_assoc] using h1.const_mul (2 * m)
    have hsin : HasDerivAt (fun t => Real.sin (2 * m * (π * t)))
        (Real.cos (2 * m * (π * x)) * (2 * m * π)) x := hg.sin
    have hdiv := hsin.div_const (2 * m * π)
    have hval : Real.cos (2 * m * (π * x)) * (2 * m * π) / (2 * m * π) =
        v' x := mul_div_cancel_right₀ _ hc0
    rw [hval] at hdiv
    exact hdiv
  have hu_deriv : ∀ x : ℝ, Real.sin (π * x) ≠ 0 →
      HasDerivAt u (u' x) x := by
    intro x hs
    have h1 : HasDerivAt (fun t : ℝ => π * t) π x := by
      simpa using (hasDerivAt_id x).const_mul π
    have hsin : HasDerivAt (fun t => Real.sin (π * t))
        (Real.cos (π * x) * π) x := h1.sin
    have hinner : HasDerivAt (fun t => 2 * Real.sin (π * t))
        (2 * (Real.cos (π * x) * π)) x := hsin.const_mul 2
    have hne : (2 : ℝ) * Real.sin (π * x) ≠ 0 :=
      mul_ne_zero two_ne_zero hs
    have hlog := hinner.log hne
    have hval : 2 * (Real.cos (π * x) * π) / (2 * Real.sin (π * x)) =
        u' x := by
      show 2 * (Real.cos (π * x) * π) / (2 * Real.sin (π * x)) =
        π * (Real.cos (π * x) / Real.sin (π * x))
      rw [mul_div_mul_left _ _ (two_ne_zero (α := ℝ)),
        mul_comm (Real.cos (π * x)) π, mul_div_assoc]
    rw [hval] at hlog
    exact hlog
  -- the identity on [ε, 1-ε]
  have hkey : ∀ ε : ℝ, ε ∈ Set.Ioo (0:ℝ) (1/2) →
      ∫ t in ε..(1-ε), u t * v' t =
        (u (1-ε) * v (1-ε) - u ε * v ε) -
          (1 / (2 * m)) * ∫ t in ε..(1-ε),
            Real.sin (2 * m * (π * t)) *
              (Real.cos (π * t) / Real.sin (π * t)) := by
    intro ε hε
    obtain ⟨hε0, hε2⟩ := hε
    have hεle : ε ≤ 1 - ε := by linarith
    have hsin_pos : ∀ x ∈ Set.uIcc ε (1-ε), 0 < Real.sin (π * x) := by
      intro x hx
      rw [Set.uIcc_of_le hεle] at hx
      apply Real.sin_pos_of_pos_of_lt_pi
      · have := hx.1
        nlinarith [Real.pi_pos]
      · nlinarith [Real.pi_pos, hx.2]
    have hu_icc : ∀ x ∈ Set.uIcc ε (1-ε), HasDerivAt u (u' x) x :=
      fun x hx => hu_deriv x (ne_of_gt (hsin_pos x hx))
    have hv_icc : ∀ x ∈ Set.uIcc ε (1-ε), HasDerivAt v (v' x) x :=
      fun x _ => hv_deriv x
    have hu'_int : IntervalIntegrable u' MeasureTheory.volume ε (1-ε) := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.div
      · exact (Continuous.continuousOn (by fun_prop))
      · exact (Continuous.continuousOn (by fun_prop))
      · exact fun x hx => ne_of_gt (hsin_pos x hx)
    have hv'_int : IntervalIntegrable v' MeasureTheory.volume ε (1-ε) :=
      ((by fun_prop : Continuous v')).intervalIntegrable _ _
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      hu_icc hv_icc hu'_int hv'_int
    rw [hibp]
    have hswap : ∫ t in ε..(1-ε), u' t * v t =
        (1 / (2 * m)) * ∫ t in ε..(1-ε),
          Real.sin (2 * m * (π * t)) *
            (Real.cos (π * t) / Real.sin (π * t)) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t ht => ?_
      have hs := ne_of_gt (hsin_pos t ht)
      show π * (Real.cos (π * t) / Real.sin (π * t)) *
        (Real.sin (2 * m * (π * t)) / (2 * m * π)) =
        1 / (2 * m) * (Real.sin (2 * m * (π * t)) *
          (Real.cos (π * t) / Real.sin (π * t)))
      field_simp
    rw [hswap]
  -- limit of the main term: primitive continuity
  have hIcc_int : IntegrableOn (fun t => u t * v' t) (Set.Icc 0 1)
      MeasureTheory.volume := by
    have h := hint_uv
    rwa [intervalIntegrable_iff_integrableOn_Icc_of_le
      (by norm_num : (0:ℝ) ≤ 1)] at h
  have hFcont : ContinuousOn (fun x => ∫ t in (0:ℝ)..x, u t * v' t)
      (Set.uIcc 0 1) := by
    apply intervalIntegral.continuousOn_primitive_interval
    rwa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  have hmem_Ioo : Set.Ioo (0:ℝ) (1/2) ∈ 𝓝[>] (0:ℝ) :=
    Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1/2)
  have htendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0)
      (𝓝[Set.uIcc (0:ℝ) 1] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact tendsto_id.mono_right nhdsWithin_le_nhds
    · filter_upwards [hmem_Ioo] with ε hε
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact ⟨hε.1.le, by linarith [hε.2]⟩
  have htendsto_one : Tendsto (fun ε : ℝ => 1 - ε) (𝓝[>] 0)
      (𝓝[Set.uIcc (0:ℝ) 1] 1) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have h : Tendsto (fun ε : ℝ => 1 - ε) (𝓝 0) (𝓝 (1 - 0)) :=
        ((by fun_prop : Continuous fun ε : ℝ => 1 - ε)).tendsto 0
      have h2 := h.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
      simpa using h2
    · filter_upwards [hmem_Ioo] with ε hε
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact ⟨by linarith [hε.2], by linarith [hε.1]⟩
  have hF0 : Tendsto (fun ε : ℝ => ∫ t in (0:ℝ)..ε, u t * v' t)
      (𝓝[>] 0) (𝓝 0) := by
    have h := (hFcont 0 (Set.left_mem_uIcc)).tendsto.comp htendsto_id
    simp only [Function.comp_def, intervalIntegral.integral_same] at h
    exact h
  have hF1 : Tendsto (fun ε : ℝ => ∫ t in (0:ℝ)..(1-ε), u t * v' t)
      (𝓝[>] 0) (𝓝 (∫ t in (0:ℝ)..1, u t * v' t)) := by
    have h := (hFcont 1 (Set.right_mem_uIcc)).tendsto.comp htendsto_one
    exact h
  have hmain : Tendsto (fun ε : ℝ => ∫ t in ε..(1-ε), u t * v' t)
      (𝓝[>] 0) (𝓝 (∫ t in (0:ℝ)..1, u t * v' t)) := by
    have hsub := hF1.sub hF0
    rw [sub_zero] at hsub
    refine Filter.Tendsto.congr' ?_ hsub
    filter_upwards [hmem_Ioo] with ε hε
    have h1 : IntervalIntegrable (fun t => u t * v' t)
        MeasureTheory.volume 0 ε := by
      apply hint_uv.mono_set
      rw [Set.uIcc_of_le hε.1.le, Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact Set.Icc_subset_Icc le_rfl (by linarith [hε.2])
    have h2 : IntervalIntegrable (fun t => u t * v' t)
        MeasureTheory.volume ε (1-ε) := by
      apply hint_uv.mono_set
      rw [Set.uIcc_of_le (by linarith [hε.1, hε.2] : ε ≤ 1-ε),
        Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact Set.Icc_subset_Icc hε.1.le (by linarith [hε.1])
    have hadd := intervalIntegral.integral_add_adjacent_intervals h1 h2
    linarith [hadd]
  -- limit of the cotangent term: primitive continuity of the kernel
  have hRcont : Continuous fun t : ℝ =>
      (1 + Real.cos (2 * (n + 1) * (π * t)) +
        2 * ∑ k ∈ Finset.range n, Real.cos (2 * (k + 1) * (π * t))) :=
    continuous_dirichlet_kernel n
  have hGcont : Continuous fun x : ℝ => ∫ t in (0:ℝ)..x,
      (1 + Real.cos (2 * (n + 1) * (π * t)) +
        2 * ∑ k ∈ Finset.range n, Real.cos (2 * (k + 1) * (π * t))) :=
    intervalIntegral.continuous_primitive
      (fun a b => hRcont.intervalIntegrable a b) 0
  have hcot_congr : ∀ ε : ℝ, ε ∈ Set.Ioo (0:ℝ) (1/2) →
      ∫ t in ε..(1-ε), Real.sin (2 * m * (π * t)) *
          (Real.cos (π * t) / Real.sin (π * t)) =
        ∫ t in ε..(1-ε),
          (1 + Real.cos (2 * (n + 1) * (π * t)) +
            2 * ∑ k ∈ Finset.range n, Real.cos (2 * (k + 1) * (π * t))) := by
    intro ε hε
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le (by linarith [hε.1, hε.2] : ε ≤ 1-ε)] at ht
    have hs : Real.sin (π * t) ≠ 0 := by
      have h : 0 < Real.sin (π * t) := by
        apply Real.sin_pos_of_pos_of_lt_pi
        · nlinarith [Real.pi_pos, ht.1, hε.1]
        · nlinarith [Real.pi_pos, ht.2, hε.1]
      exact ne_of_gt h
    have h := sin_two_succ_mul_mul_cot hs n
    calc Real.sin (2 * m * (π * t)) *
        (Real.cos (π * t) / Real.sin (π * t))
        = Real.sin (2 * (n + 1) * (π * t)) *
          (Real.cos (π * t) / Real.sin (π * t)) := by rw [hm]
      _ = 1 + Real.cos (2 * (n + 1) * (π * t)) +
          2 * ∑ k ∈ Finset.range n, Real.cos (2 * (k + 1) * (π * t)) := h
  have hcot_lim : Tendsto (fun ε : ℝ => ∫ t in ε..(1-ε),
      Real.sin (2 * m * (π * t)) *
        (Real.cos (π * t) / Real.sin (π * t))) (𝓝[>] 0) (𝓝 1) := by
    have hG0 := (hGcont.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    have hG1 : Tendsto (fun ε : ℝ => ∫ t in (0:ℝ)..(1-ε),
        (1 + Real.cos (2 * (n + 1) * (π * t)) +
          2 * ∑ k ∈ Finset.range n, Real.cos (2 * (k + 1) * (π * t))))
        (𝓝[>] 0) (𝓝 (∫ t in (0:ℝ)..1,
          (1 + Real.cos (2 * (n + 1) * (π * t)) +
            2 * ∑ k ∈ Finset.range n,
              Real.cos (2 * (k + 1) * (π * t))))) := by
      have hcomp : Tendsto (fun ε : ℝ => 1 - ε) (𝓝[>] 0) (𝓝 (1:ℝ)) := by
        have h : Tendsto (fun ε : ℝ => 1 - ε) (𝓝 0) (𝓝 (1 - 0)) :=
          ((by fun_prop : Continuous fun ε : ℝ => 1 - ε)).tendsto 0
        have h2 := h.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
        simpa using h2
      exact (hGcont.tendsto 1).comp hcomp
    have hsub := hG1.sub hG0
    simp only [intervalIntegral.integral_same, sub_zero,
      integral_dirichlet_kernel_eq_one n] at hsub
    refine Filter.Tendsto.congr' ?_ hsub
    filter_upwards [hmem_Ioo] with ε hε
    rw [hcot_congr ε hε]
    have h1 : IntervalIntegrable (fun t =>
        (1 + Real.cos (2 * (n + 1) * (π * t)) +
          2 * ∑ k ∈ Finset.range n, Real.cos (2 * (k + 1) * (π * t))))
        MeasureTheory.volume 0 ε := hRcont.intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun t =>
        (1 + Real.cos (2 * (n + 1) * (π * t)) +
          2 * ∑ k ∈ Finset.range n, Real.cos (2 * (k + 1) * (π * t))))
        MeasureTheory.volume ε (1-ε) := hRcont.intervalIntegrable _ _
    have hadd := intervalIntegral.integral_add_adjacent_intervals h1 h2
    linarith [hadd]
  -- limit of the boundary term
  have habs_sin : ∀ z : ℝ, |Real.sin z| ≤ |z| := fun z => by
    have h := Real.abs_sin_sub_sin_le z 0
    simpa using h
  have hbdry : Tendsto (fun ε : ℝ =>
      u (1-ε) * v (1-ε) - u ε * v ε) (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm'
      (a := fun ε => 2 * (7 * Real.sqrt ε + 2 * ε))
    · filter_upwards [hmem_Ioo] with ε hε
      obtain ⟨hε0, hε2⟩ := hε
      have hε1 : ε ≤ 1 := by linarith
      -- |v y| ≤ ε at both boundary points
      have hv_bound : ∀ y : ℝ, |Real.sin (2 * m * (π * y))| ≤ 2 * m * π * ε →
          |v y| ≤ ε := by
        intro y hy
        rw [hv_def]
        rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * m * π),
          div_le_iff₀ (by positivity : (0:ℝ) < 2 * m * π)]
        calc |Real.sin (2 * m * (π * y))| ≤ 2 * m * π * ε := hy
          _ = ε * (2 * m * π) := by ring
      have hvε : |v ε| ≤ ε := by
        apply hv_bound
        calc |Real.sin (2 * m * (π * ε))| ≤ |2 * m * (π * ε)| :=
              habs_sin _
          _ = 2 * m * π * ε := by
              rw [abs_of_pos (by positivity)]
              ring
      have hv1ε : |v (1-ε)| ≤ ε := by
        apply hv_bound
        have harg : 2 * m * (π * (1 - ε)) =
            2 * m * π - 2 * m * (π * ε) := by ring
        have hper : Real.sin (2 * m * (π * (1 - ε))) =
            -Real.sin (2 * m * (π * ε) - 2 * m * π) := by
          rw [harg, show 2 * m * π - 2 * m * (π * ε) =
            -(2 * m * (π * ε) - 2 * m * π) by ring, Real.sin_neg]
        rw [hper, abs_neg]
        have hshift : Real.sin (2 * m * (π * ε) - 2 * m * π) =
            Real.sin (2 * m * (π * ε)) := by
          rw [hm]
          have := Real.sin_sub_int_mul_two_pi (2 * ((n:ℝ) + 1) * (π * ε))
            ((n : ℤ) + 1)
          calc Real.sin (2 * ((n:ℝ) + 1) * (π * ε) - 2 * ((n:ℝ) + 1) * π)
              = Real.sin (2 * ((n:ℝ) + 1) * (π * ε) -
                  (((n : ℤ) + 1 : ℤ) : ℝ) * (2 * π)) := by
                congr 1
                push_cast
                ring
            _ = Real.sin (2 * ((n:ℝ) + 1) * (π * ε)) := this
        rw [hshift]
        calc |Real.sin (2 * m * (π * ε))| ≤ |2 * m * (π * ε)| :=
              habs_sin _
          _ = 2 * m * π * ε := by
              rw [abs_of_pos (by positivity)]
              ring
      -- |u| at both boundary points
      have huε : |u ε| ≤ |Real.log ε| + 2 := by
        rw [hu_def]
        exact abs_log_two_sin_le hε0 hε2.le
      have hu1ε : |u (1-ε)| ≤ |Real.log ε| + 2 := by
        rw [hu_def]
        have hsym : Real.sin (π * (1 - ε)) = Real.sin (π * ε) := by
          rw [show π * (1 - ε) = π - π * ε by ring, Real.sin_pi_sub]
        show |Real.log (2 * Real.sin (π * (1 - ε)))| ≤ |Real.log ε| + 2
        rw [hsym]
        exact abs_log_two_sin_le hε0 hε2.le
      -- assemble
      have hεlog : ε * (|Real.log ε| + 2) ≤ 7 * Real.sqrt ε + 2 * ε := by
        have h := eps_mul_abs_log_le_sqrt hε0 hε1
        nlinarith
      have habs1 : |u (1-ε) * v (1-ε)| ≤ 7 * Real.sqrt ε + 2 * ε := by
        rw [abs_mul]
        calc |u (1-ε)| * |v (1-ε)| ≤ (|Real.log ε| + 2) * ε := by
              apply mul_le_mul hu1ε hv1ε (abs_nonneg _)
              positivity
          _ = ε * (|Real.log ε| + 2) := by ring
          _ ≤ 7 * Real.sqrt ε + 2 * ε := hεlog
      have habs2 : |u ε * v ε| ≤ 7 * Real.sqrt ε + 2 * ε := by
        rw [abs_mul]
        calc |u ε| * |v ε| ≤ (|Real.log ε| + 2) * ε := by
              apply mul_le_mul huε hvε (abs_nonneg _)
              positivity
          _ = ε * (|Real.log ε| + 2) := by ring
          _ ≤ 7 * Real.sqrt ε + 2 * ε := hεlog
      calc ‖u (1-ε) * v (1-ε) - u ε * v ε‖
          ≤ ‖u (1-ε) * v (1-ε)‖ + ‖u ε * v ε‖ := norm_sub_le _ _
        _ ≤ (7 * Real.sqrt ε + 2 * ε) + (7 * Real.sqrt ε + 2 * ε) := by
            simp only [Real.norm_eq_abs]
            exact add_le_add habs1 habs2
        _ = 2 * (7 * Real.sqrt ε + 2 * ε) := by ring
    · have hcont : Continuous fun ε : ℝ =>
          2 * (7 * Real.sqrt ε + 2 * ε) :=
        (((Real.continuous_sqrt.const_mul 7).add
          (continuous_id.const_mul 2)).const_mul 2)
      have h := hcont.tendsto 0
      have h2 := h.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
      have h3 : (2 : ℝ) * (7 * Real.sqrt 0 + 2 * 0) = 0 := by
        simp
      rw [h3] at h2
      exact h2
  -- assemble the limits
  have hRHS : Tendsto (fun ε : ℝ =>
      (u (1-ε) * v (1-ε) - u ε * v ε) -
        (1 / (2 * m)) * ∫ t in ε..(1-ε),
          Real.sin (2 * m * (π * t)) *
            (Real.cos (π * t) / Real.sin (π * t)))
      (𝓝[>] 0) (𝓝 (0 - (1 / (2 * m)) * 1)) :=
    hbdry.sub ((hcot_lim.const_mul (1 / (2 * m))))
  have hLHS : Tendsto (fun ε : ℝ =>
      (u (1-ε) * v (1-ε) - u ε * v ε) -
        (1 / (2 * m)) * ∫ t in ε..(1-ε),
          Real.sin (2 * m * (π * t)) *
            (Real.cos (π * t) / Real.sin (π * t)))
      (𝓝[>] 0) (𝓝 (∫ t in (0:ℝ)..1, u t * v' t)) := by
    apply hmain.congr'
    filter_upwards [hmem_Ioo] with ε hε
    exact hkey ε hε
  have huniq := tendsto_nhds_unique hLHS hRHS
  show ∫ t in (0:ℝ)..1, u t * v' t = -(1 / (2 * m))
  rw [huniq]
  ring

/-- **The sine pairing vanishes by reflection symmetry**:
`∫₀¹ log (2 sin πt)·sin (2(n+1)·πt) dt = 0` — the integrand is odd
under `t ↦ 1−t`.  Together with `integral_log_two_sin_mul_cos` this
determines every Fourier coefficient of the doubling cocycle:
`ψ̂(n) = −1/(2|n|)` for `n ≠ 0`, `ψ̂(0) = 0`. -/
theorem integral_log_two_sin_mul_sin (n : ℕ) :
    ∫ t in (0:ℝ)..1, Real.log (2 * Real.sin (π * t)) *
      Real.sin (2 * (n + 1) * (π * t)) = 0 := by
  refine integral_unit_eq_zero_of_reflect_neg fun x => ?_
  show Real.log (2 * Real.sin (π * (1 - x))) *
    Real.sin (2 * (n + 1) * (π * (1 - x))) =
    -(Real.log (2 * Real.sin (π * x)) *
      Real.sin (2 * (n + 1) * (π * x)))
  have h1 : Real.sin (π * (1 - x)) = Real.sin (π * x) := by
    rw [show π * (1 - x) = π - π * x by ring, Real.sin_pi_sub]
  have h2 : Real.sin (2 * (n + 1) * (π * (1 - x))) =
      -Real.sin (2 * (n + 1) * (π * x)) := by
    have harg : 2 * ((n:ℝ) + 1) * (π * (1 - x)) =
        -(2 * ((n:ℝ) + 1) * (π * x)) + ((n:ℤ) + 1 : ℤ) * (2 * π) := by
      push_cast
      ring
    rw [harg, Real.sin_add_int_mul_two_pi, Real.sin_neg]
  rw [h1, h2]
  ring

end Fabius
