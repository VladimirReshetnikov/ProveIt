import FabiusFunction.LogSineFourierCoefficient
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ZetaValues

/-!
# The Clausen value: `∫₀¹ log (2 sin πt)² dt = π²/12`

Parseval's identity on the interval (`tsum_sq_fourierCoeffOn`) applied
to the doubling cocycle `ψ = log (2 sin π·)`, whose full Fourier data
is now known:

`ψ̂(0) = 0` (`LogSineMeanZero`), and for `m ≥ 1`
`ψ̂(±m) = −1/(2m)` (`LogSineFourierCoefficient`, both pairings).

Summing `‖ψ̂‖²` over `ℤ` gives `2·(1/4)·ζ(2) = π²/12` by Basel
(`hasSum_zeta_two`), so

`∫₀¹ log (2 sin πt)² dt = π²/12` — the audits' `c₀` for the cocycle,
the first of Document 6's two Clausen values.

* `intervalIntegrable_log_two_sin_mul_sin_pairing` — integrability of
  the sine pairing.
* `fourierCoeffOn_log_two_sin_zero/_pos/_neg` — the coefficients.
* `integral_sq_log_two_sin_pi_mul` — **the Clausen value `π²/12`**.
-/

set_option autoImplicit false

open Filter Topology intervalIntegral Real MeasureTheory Set

namespace Fabius

/-- The sine pairing is integrable (same domination as the cosine). -/
theorem intervalIntegrable_log_two_sin_mul_sin_pairing (n : ℕ) :
    IntervalIntegrable (fun t => Real.log (2 * Real.sin (π * t)) *
      Real.sin (2 * (n + 1) * (π * t))) MeasureTheory.volume 0 1 := by
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
    have hsin : |Real.sin (2 * (n + 1) * (π * t))| ≤ 1 :=
      Real.abs_sin_le_one _
    have hA : |A| ≤ (1 + A ^ 2) / 2 := by
      nlinarith [sq_nonneg (|A| - 1), sq_abs A, abs_nonneg A]
    calc |A| * |Real.sin (2 * (n + 1) * (π * t))| ≤ |A| * 1 :=
          mul_le_mul_of_nonneg_left hsin (abs_nonneg _)
      _ = |A| := mul_one _
      _ ≤ (1 + A ^ 2) / 2 := hA

/-- The exponential pairing of the cocycle at signed integer
frequency: for `s = ±1`,
`∫₀¹ exp(i·s·2(m+1)πx)·ψ(x) dx = −1/(2(m+1))`. -/
theorem integral_exp_mul_log_two_sin (s : ℝ) (hs : s = 1 ∨ s = -1)
    (m : ℕ) :
    ∫ x in (0:ℝ)..1,
      Complex.exp (((s * (2 * (m + 1) * (π * x)) : ℝ) : ℂ) * Complex.I) *
        (Real.log (2 * Real.sin (π * x)) : ℂ) =
      ((-(1 / (2 * (m + 1))) : ℝ) : ℂ) := by
  have hcos_int := intervalIntegrable_log_two_sin_mul_cos m
  have hsin_int := intervalIntegrable_log_two_sin_mul_sin_pairing m
  -- pointwise split into real and imaginary parts
  have hsplit : ∀ x : ℝ,
      Complex.exp (((s * (2 * (m + 1) * (π * x)) : ℝ) : ℂ) * Complex.I) *
        (Real.log (2 * Real.sin (π * x)) : ℂ) =
      ((Real.log (2 * Real.sin (π * x)) *
          Real.cos (2 * (m + 1) * (π * x)) : ℝ) : ℂ) +
        ((s * (Real.log (2 * Real.sin (π * x)) *
          Real.sin (2 * (m + 1) * (π * x))) : ℝ) : ℂ) * Complex.I := by
    intro x
    rw [Complex.exp_ofReal_mul_I]
    rcases hs with rfl | rfl
    · push_cast
      simp only [one_mul]
      ring
    · rw [show (-1 : ℝ) * (2 * ((m:ℝ) + 1) * (π * x)) =
        -(2 * ((m:ℝ) + 1) * (π * x)) by ring, Real.cos_neg,
        Real.sin_neg]
      push_cast
      ring
  rw [intervalIntegral.integral_congr (fun x _ => hsplit x)]
  have h1 : IntervalIntegrable (fun x =>
      ((Real.log (2 * Real.sin (π * x)) *
        Real.cos (2 * (m + 1) * (π * x)) : ℝ) : ℂ))
      MeasureTheory.volume 0 1 := by
    rw [intervalIntegrable_iff] at hcos_int ⊢
    exact hcos_int.ofReal
  have h2 : IntervalIntegrable (fun x =>
      ((s * (Real.log (2 * Real.sin (π * x)) *
        Real.sin (2 * (m + 1) * (π * x))) : ℝ) : ℂ) * Complex.I)
      MeasureTheory.volume 0 1 := by
    rw [intervalIntegrable_iff]
    apply Integrable.mul_const
    rw [intervalIntegrable_iff] at hsin_int
    exact (hsin_int.const_mul s).ofReal
  rw [intervalIntegral.integral_add h1 h2,
    intervalIntegral.integral_mul_const]
  have hre : ∫ x in (0:ℝ)..1,
      ((Real.log (2 * Real.sin (π * x)) *
        Real.cos (2 * (m + 1) * (π * x)) : ℝ) : ℂ) =
      ((-(1 / (2 * (m + 1))) : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_ofReal, integral_log_two_sin_mul_cos m]
  have him : ∫ x in (0:ℝ)..1,
      ((s * (Real.log (2 * Real.sin (π * x)) *
        Real.sin (2 * (m + 1) * (π * x))) : ℝ) : ℂ) = 0 := by
    rw [intervalIntegral.integral_ofReal]
    have h := integral_log_two_sin_mul_sin m
    rw [intervalIntegral.integral_const_mul, h]
    norm_num
  rw [hre, him]
  ring

/-- `ψ̂(0) = 0`: the cocycle has mean zero. -/
theorem fourierCoeffOn_log_two_sin_zero :
    fourierCoeffOn (zero_lt_one) (fun t : ℝ =>
      (Real.log (2 * Real.sin (π * t)) : ℂ)) (0 : ℤ) = 0 := by
  rw [fourierCoeffOn_eq_integral]
  have hcongr : ∫ x in (0:ℝ)..1, fourier (-(0:ℤ))
      (x : AddCircle ((1:ℝ) - 0)) •
      ((Real.log (2 * Real.sin (π * x)) : ℂ)) =
      ∫ x in (0:ℝ)..1, ((Real.log (2 * Real.sin (π * x)) : ℝ) : ℂ) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [neg_zero, fourier_zero, one_smul]
  rw [hcongr, intervalIntegral.integral_ofReal,
    integral_log_two_sin_pi_mul]
  simp

/-- `ψ̂(m+1) = −1/(2(m+1))`. -/
theorem fourierCoeffOn_log_two_sin_pos (m : ℕ) :
    fourierCoeffOn (zero_lt_one) (fun t : ℝ =>
      (Real.log (2 * Real.sin (π * t)) : ℂ)) ((m : ℤ) + 1) =
      ((-(1 / (2 * (m + 1))) : ℝ) : ℂ) := by
  rw [fourierCoeffOn_eq_integral]
  have hcongr : ∫ x in (0:ℝ)..1, fourier (-((m : ℤ) + 1))
      (x : AddCircle ((1:ℝ) - 0)) •
      ((Real.log (2 * Real.sin (π * x)) : ℂ)) =
      ∫ x in (0:ℝ)..1,
        Complex.exp ((((-1 : ℝ) * (2 * (m + 1) * (π * x)) : ℝ) : ℂ) *
          Complex.I) * (Real.log (2 * Real.sin (π * x)) : ℂ) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [fourier_coe_apply, smul_eq_mul]
    congr 2
    push_cast
    ring
  rw [hcongr, integral_exp_mul_log_two_sin (-1) (Or.inr rfl) m]
  norm_num

/-- `ψ̂(−(m+1)) = −1/(2(m+1))`. -/
theorem fourierCoeffOn_log_two_sin_neg (m : ℕ) :
    fourierCoeffOn (zero_lt_one) (fun t : ℝ =>
      (Real.log (2 * Real.sin (π * t)) : ℂ)) (-((m : ℤ) + 1)) =
      ((-(1 / (2 * (m + 1))) : ℝ) : ℂ) := by
  rw [fourierCoeffOn_eq_integral]
  have hcongr : ∫ x in (0:ℝ)..1, fourier (-(-((m : ℤ) + 1)))
      (x : AddCircle ((1:ℝ) - 0)) •
      ((Real.log (2 * Real.sin (π * x)) : ℂ)) =
      ∫ x in (0:ℝ)..1,
        Complex.exp ((((1 : ℝ) * (2 * (m + 1) * (π * x)) : ℝ) : ℂ) *
          Complex.I) * (Real.log (2 * Real.sin (π * x)) : ℂ) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [fourier_coe_apply, smul_eq_mul]
    congr 2
    push_cast
    ring
  rw [hcongr, integral_exp_mul_log_two_sin 1 (Or.inl rfl) m]
  norm_num

/-- **The Clausen value**: `∫₀¹ log (2 sin πt)² dt = π²/12` — Parseval
over the now-complete Fourier data of the doubling cocycle, plus
Basel. -/
theorem integral_sq_log_two_sin_pi_mul :
    ∫ t in (0:ℝ)..1, Real.log (2 * Real.sin (π * t)) ^ 2 = π ^ 2 / 12 := by
  -- membership in L²
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => Real.log (2 * Real.sin (π * t)))
      (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    measurable_log_two_sin_pi_mul.aestronglyMeasurable
  have hint : Integrable
      (fun t : ℝ => Real.log (2 * Real.sin (π * t)) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    intervalIntegrable_sq_log_two_sin_pi_mul.1
  have hL2R : MemLp (fun t : ℝ => Real.log (2 * Real.sin (π * t))) 2
      (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    (memLp_two_iff_integrable_sq hmeas).mpr hint
  have hL2 : MemLp (fun t : ℝ =>
      (Real.log (2 * Real.sin (π * t)) : ℂ)) 2
      (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1)) := hL2R.ofReal
  -- Parseval
  have hpars := tsum_sq_fourierCoeffOn zero_lt_one hL2
  -- the coefficient-square function
  set c : ℤ → ℝ := fun i => ‖fourierCoeffOn (zero_lt_one) (fun t : ℝ =>
    (Real.log (2 * Real.sin (π * t)) : ℂ)) i‖ ^ 2 with hc
  -- values of the halves
  have hnorm : ∀ m : ℕ, ‖(((-(1 / (2 * (m + 1)))) : ℝ) : ℂ)‖ ^ 2 =
      1 / 4 * (1 / ((m : ℝ) + 1) ^ 2) := by
    intro m
    rw [Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * (m + 1)))]
    field_simp
    ring
  have hposc : ∀ m : ℕ, c ((m : ℤ) + 1) =
      1 / 4 * (1 / ((m : ℝ) + 1) ^ 2) := by
    intro m
    rw [hc]
    simp only
    rw [fourierCoeffOn_log_two_sin_pos m, hnorm m]
  have hnegc : ∀ m : ℕ, c (-((m : ℤ) + 1)) =
      1 / 4 * (1 / ((m : ℝ) + 1) ^ 2) := by
    intro m
    rw [hc]
    simp only
    rw [fourierCoeffOn_log_two_sin_neg m, hnorm m]
  have hzeroc : c 0 = 0 := by
    rw [hc]
    simp only
    rw [fourierCoeffOn_log_two_sin_zero]
    simp
  -- Basel halves
  have hbasel : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
    have h2 : HasSum (fun n : ℕ => (1:ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2)
        (π ^ 2 / 6) := by
      apply (hasSum_nat_add_iff (f := fun n : ℕ => (1:ℝ) / (n:ℝ) ^ 2)
        (g := π ^ 2 / 6) 1).mpr
      have hz : (π ^ 2 / 6 : ℝ) + ∑ i ∈ Finset.range 1,
          (1:ℝ) / (i:ℝ) ^ 2 = π ^ 2 / 6 := by
        simp
      rw [hz]
      exact hasSum_zeta_two
    have h4 : (fun n : ℕ => (1:ℝ) / ((n:ℝ) + 1) ^ 2) =
        fun n : ℕ => (1:ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 := by
      funext n
      push_cast
      ring
    rw [h4]
    exact h2
  have hhalf : HasSum (fun n : ℕ => c ((n : ℤ) + 1)) (π ^ 2 / 24) := by
    have h := hbasel.mul_left (1 / 4)
    have hval : (1:ℝ) / 4 * (π ^ 2 / 6) = π ^ 2 / 24 := by ring
    rw [hval] at h
    have heq : (fun n : ℕ => 1 / 4 * (1 / ((n : ℝ) + 1) ^ 2)) =
        fun n : ℕ => c ((n : ℤ) + 1) := by
      funext n
      rw [hposc n]
    rw [heq] at h
    exact h
  have hhalf' : HasSum (fun n : ℕ => c (-((n : ℤ) + 1))) (π ^ 2 / 24) := by
    have h := hbasel.mul_left (1 / 4)
    have hval : (1:ℝ) / 4 * (π ^ 2 / 6) = π ^ 2 / 24 := by ring
    rw [hval] at h
    have heq : (fun n : ℕ => 1 / 4 * (1 / ((n : ℝ) + 1) ^ 2)) =
        fun n : ℕ => c (-((n : ℤ) + 1)) := by
      funext n
      rw [hnegc n]
    rw [heq] at h
    exact h
  have hsum : HasSum c (π ^ 2 / 24 + c 0 + π ^ 2 / 24) :=
    HasSum.of_add_one_of_neg_add_one hhalf hhalf'
  have htsum : ∑' i : ℤ, c i = π ^ 2 / 12 := by
    rw [hsum.tsum_eq, hzeroc]
    ring
  -- assemble
  rw [htsum] at hpars
  have hnorm2 : ∀ x : ℝ, ‖((Real.log (2 * Real.sin (π * x)) : ℝ) : ℂ)‖ ^ 2 =
      Real.log (2 * Real.sin (π * x)) ^ 2 := by
    intro x
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hcongr : ∫ x in (0:ℝ)..1,
      ‖((Real.log (2 * Real.sin (π * x)) : ℝ) : ℂ)‖ ^ 2 =
      ∫ x in (0:ℝ)..1, Real.log (2 * Real.sin (π * x)) ^ 2 :=
    intervalIntegral.integral_congr fun x _ => hnorm2 x
  rw [hcongr] at hpars
  have hsmul : ((1:ℝ) - 0)⁻¹ •
      (∫ x in (0:ℝ)..1, Real.log (2 * Real.sin (π * x)) ^ 2) =
      ∫ x in (0:ℝ)..1, Real.log (2 * Real.sin (π * x)) ^ 2 := by
    norm_num
  rw [hsmul] at hpars
  linarith [hpars]

end Fabius
