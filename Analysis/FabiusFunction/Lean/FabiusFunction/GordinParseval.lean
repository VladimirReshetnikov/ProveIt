import FabiusFunction.LogCosineFourier

/-!
# The variance constant: `∫₀¹ log |tan πt|² dt = π²/4`

Parseval for the Gordin observable `d = log |tan π·|`, closing the
audits' variance layer.  The Fourier data of `d` is complete
(`LogCosineFourier`): `d̂(0) = 0` and
`d̂(±m) = −(1 − (−1)^m)/(2m)` — supported on odd frequencies with
value `−1/m` there.  Parseval and the odd Basel sum
`∑ 1/(2k+1)² = π²/8` give

`σ² = ∫₀¹ d² = 2·(π²/8) = π²/4`,

the exact variance constant of Document 6's central limit theorem and
law of the iterated logarithm (`σ = π/2`, LIL constant `π/√2`).

* `intervalIntegrable_log_abs_tan_mul` — pairings of `d` against
  bounded continuous detectors.
* `integral_exp_mul_log_abs_tan` — the exponential pairing.
* `fourierCoeffOn_log_abs_tan_zero/_pos/_neg` — the coefficients.
* `hasSum_odd_sq_inv` — the odd Basel sum `π²/8`.
* `integral_sq_log_abs_tan_pi_mul` — **the variance `π²/4`**.
-/

set_option autoImplicit false

open Filter Topology intervalIntegral Real MeasureTheory Set

namespace Fabius

/-- The Gordin observable paired with any bounded continuous detector
is integrable. -/
theorem intervalIntegrable_log_abs_tan_mul (g : ℝ → ℝ)
    (hg : Continuous g) (hb : ∀ x, |g x| ≤ 1) :
    IntervalIntegrable (fun t => Real.log |Real.tan (π * t)| * g t)
      MeasureTheory.volume 0 1 := by
  have hdom : IntervalIntegrable
      (fun t => (1 + Real.log |Real.tan (π * t)| ^ 2) / 2)
      MeasureTheory.volume 0 1 :=
    (intervalIntegrable_const.add
      intervalIntegrable_sq_log_abs_tan_pi_mul).div_const 2
  apply hdom.mono_fun
  · exact (measurable_log_abs_tan_pi_mul.mul
      hg.measurable).aestronglyMeasurable
  · filter_upwards with t
    set A := Real.log |Real.tan (π * t)|
    simp only [Real.norm_eq_abs]
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 + A ^ 2) / 2)]
    have hA : |A| ≤ (1 + A ^ 2) / 2 := by
      nlinarith [sq_nonneg (|A| - 1), sq_abs A, abs_nonneg A]
    calc |A| * |g t| ≤ |A| * 1 :=
          mul_le_mul_of_nonneg_left (hb t) (abs_nonneg _)
      _ = |A| := mul_one _
      _ ≤ (1 + A ^ 2) / 2 := hA

/-- The exponential pairing of the Gordin observable at signed integer
frequency. -/
theorem integral_exp_mul_log_abs_tan (s : ℝ) (hs : s = 1 ∨ s = -1)
    (m : ℕ) :
    ∫ x in (0:ℝ)..1,
      Complex.exp (((s * (2 * (m + 1) * (π * x)) : ℝ) : ℂ) * Complex.I) *
        (Real.log |Real.tan (π * x)| : ℂ) =
      ((-(1 / (2 * (m + 1))) * (1 - (-1) ^ (m + 1)) : ℝ) : ℂ) := by
  have hcos_int := intervalIntegrable_log_abs_tan_mul
    (fun x => Real.cos (2 * (m + 1) * (π * x))) (by fun_prop)
    (fun x => Real.abs_cos_le_one _)
  have hsin_int := intervalIntegrable_log_abs_tan_mul
    (fun x => Real.sin (2 * (m + 1) * (π * x))) (by fun_prop)
    (fun x => Real.abs_sin_le_one _)
  have hsplit : ∀ x : ℝ,
      Complex.exp (((s * (2 * (m + 1) * (π * x)) : ℝ) : ℂ) * Complex.I) *
        (Real.log |Real.tan (π * x)| : ℂ) =
      ((Real.log |Real.tan (π * x)| *
          Real.cos (2 * (m + 1) * (π * x)) : ℝ) : ℂ) +
        ((s * (Real.log |Real.tan (π * x)| *
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
      ((Real.log |Real.tan (π * x)| *
        Real.cos (2 * (m + 1) * (π * x)) : ℝ) : ℂ))
      MeasureTheory.volume 0 1 := by
    rw [intervalIntegrable_iff] at hcos_int ⊢
    exact hcos_int.ofReal
  have h2 : IntervalIntegrable (fun x =>
      ((s * (Real.log |Real.tan (π * x)| *
        Real.sin (2 * (m + 1) * (π * x))) : ℝ) : ℂ) * Complex.I)
      MeasureTheory.volume 0 1 := by
    rw [intervalIntegrable_iff]
    apply Integrable.mul_const
    rw [intervalIntegrable_iff] at hsin_int
    exact (hsin_int.const_mul s).ofReal
  rw [intervalIntegral.integral_add h1 h2,
    intervalIntegral.integral_mul_const]
  have hre : ∫ x in (0:ℝ)..1,
      ((Real.log |Real.tan (π * x)| *
        Real.cos (2 * (m + 1) * (π * x)) : ℝ) : ℂ) =
      ((-(1 / (2 * (m + 1))) * (1 - (-1) ^ (m + 1)) : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_ofReal, integral_log_abs_tan_mul_cos m]
  have him : ∫ x in (0:ℝ)..1,
      ((s * (Real.log |Real.tan (π * x)| *
        Real.sin (2 * (m + 1) * (π * x))) : ℝ) : ℂ) = 0 := by
    rw [intervalIntegral.integral_ofReal]
    rw [intervalIntegral.integral_const_mul, integral_log_abs_tan_mul_sin m]
    norm_num
  rw [hre, him]
  ring

/-- `d̂(0) = 0`. -/
theorem fourierCoeffOn_log_abs_tan_zero :
    fourierCoeffOn (zero_lt_one) (fun t : ℝ =>
      (Real.log |Real.tan (π * t)| : ℂ)) (0 : ℤ) = 0 := by
  rw [fourierCoeffOn_eq_integral]
  have hcongr : ∫ x in (0:ℝ)..1, fourier (-(0:ℤ))
      (x : AddCircle ((1:ℝ) - 0)) •
      ((Real.log |Real.tan (π * x)| : ℂ)) =
      ∫ x in (0:ℝ)..1, ((Real.log |Real.tan (π * x)| : ℝ) : ℂ) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [neg_zero, fourier_zero, one_smul]
  rw [hcongr, intervalIntegral.integral_ofReal,
    integral_log_abs_tan_pi_mul]
  simp

/-- `d̂(m+1) = −(1 − (−1)^{m+1})/(2(m+1))`. -/
theorem fourierCoeffOn_log_abs_tan_pos (m : ℕ) :
    fourierCoeffOn (zero_lt_one) (fun t : ℝ =>
      (Real.log |Real.tan (π * t)| : ℂ)) ((m : ℤ) + 1) =
      ((-(1 / (2 * (m + 1))) * (1 - (-1) ^ (m + 1)) : ℝ) : ℂ) := by
  rw [fourierCoeffOn_eq_integral]
  have hcongr : ∫ x in (0:ℝ)..1, fourier (-((m : ℤ) + 1))
      (x : AddCircle ((1:ℝ) - 0)) •
      ((Real.log |Real.tan (π * x)| : ℂ)) =
      ∫ x in (0:ℝ)..1,
        Complex.exp ((((-1 : ℝ) * (2 * (m + 1) * (π * x)) : ℝ) : ℂ) *
          Complex.I) * (Real.log |Real.tan (π * x)| : ℂ) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [fourier_coe_apply, smul_eq_mul]
    congr 2
    push_cast
    ring
  rw [hcongr, integral_exp_mul_log_abs_tan (-1) (Or.inr rfl) m]
  norm_num

/-- `d̂(−(m+1)) = −(1 − (−1)^{m+1})/(2(m+1))`. -/
theorem fourierCoeffOn_log_abs_tan_neg (m : ℕ) :
    fourierCoeffOn (zero_lt_one) (fun t : ℝ =>
      (Real.log |Real.tan (π * t)| : ℂ)) (-((m : ℤ) + 1)) =
      ((-(1 / (2 * (m + 1))) * (1 - (-1) ^ (m + 1)) : ℝ) : ℂ) := by
  rw [fourierCoeffOn_eq_integral]
  have hcongr : ∫ x in (0:ℝ)..1, fourier (-(-((m : ℤ) + 1)))
      (x : AddCircle ((1:ℝ) - 0)) •
      ((Real.log |Real.tan (π * x)| : ℂ)) =
      ∫ x in (0:ℝ)..1,
        Complex.exp ((((1 : ℝ) * (2 * (m + 1) * (π * x)) : ℝ) : ℂ) *
          Complex.I) * (Real.log |Real.tan (π * x)| : ℂ) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [fourier_coe_apply, smul_eq_mul]
    congr 2
    push_cast
    ring
  rw [hcongr, integral_exp_mul_log_abs_tan 1 (Or.inl rfl) m]
  norm_num

/-- Basel over the naturals shifted by one. -/
theorem hasSum_one_div_succ_sq :
    HasSum (fun n : ℕ => (1:ℝ) / ((n : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
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

/-- **The odd Basel sum**: `∑ 1/(2k+1)² = π²/8`. -/
theorem hasSum_odd_sq_inv :
    HasSum (fun k : ℕ => (1:ℝ) / (2 * (k : ℝ) + 1) ^ 2) (π ^ 2 / 8) := by
  set f : ℕ → ℝ := fun n => (1:ℝ) / ((n : ℝ) + 1) ^ 2 with hf
  have htotal : HasSum f (π ^ 2 / 6) := hasSum_one_div_succ_sq
  have hev : HasSum (fun k : ℕ => f (2 * k + 1)) (π ^ 2 / 24) := by
    have h := htotal.mul_left (1 / 4)
    have hval : (1:ℝ) / 4 * (π ^ 2 / 6) = π ^ 2 / 24 := by ring
    rw [hval] at h
    have heq : (fun n : ℕ => 1 / 4 * f n) =
        fun k : ℕ => f (2 * k + 1) := by
      funext k
      rw [hf]
      simp only
      push_cast
      field_simp
      ring
    rw [heq] at h
    exact h
  have hsummable : Summable (fun k : ℕ => f (2 * k)) :=
    htotal.summable.comp_injective
      (mul_right_injective₀ (two_ne_zero (α := ℕ)))
  have ho := hsummable.hasSum
  have htot2 := HasSum.even_add_odd ho hev
  have huniq := htot2.unique htotal
  have hval : (∑' k : ℕ, f (2 * k)) = π ^ 2 / 8 := by linarith
  have hres : HasSum (fun k : ℕ => f (2 * k)) (π ^ 2 / 8) := hval ▸ ho
  have hfun : (fun k : ℕ => f (2 * k)) =
      fun k : ℕ => (1:ℝ) / (2 * (k : ℝ) + 1) ^ 2 := by
    funext k
    rw [hf]
    simp only
    push_cast
    ring_nf
  rw [hfun] at hres
  exact hres

set_option maxHeartbeats 4000000 in
/-- **The variance constant**: `∫₀¹ log |tan πt|² dt = π²/4` — the
exact `σ²` of the audits' Gordin CLT/LIL. -/
theorem integral_sq_log_abs_tan_pi_mul :
    ∫ t in (0:ℝ)..1, Real.log |Real.tan (π * t)| ^ 2 = π ^ 2 / 4 := by
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => Real.log |Real.tan (π * t)|)
      (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    measurable_log_abs_tan_pi_mul.aestronglyMeasurable
  have hint : Integrable
      (fun t : ℝ => Real.log |Real.tan (π * t)| ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    intervalIntegrable_sq_log_abs_tan_pi_mul.1
  have hL2R : MemLp (fun t : ℝ => Real.log |Real.tan (π * t)|) 2
      (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    (memLp_two_iff_integrable_sq hmeas).mpr hint
  have hL2 : MemLp (fun t : ℝ =>
      (Real.log |Real.tan (π * t)| : ℂ)) 2
      (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1)) := hL2R.ofReal
  have hpars := tsum_sq_fourierCoeffOn zero_lt_one hL2
  set c : ℤ → ℝ := fun i => ‖fourierCoeffOn (zero_lt_one) (fun t : ℝ =>
    (Real.log |Real.tan (π * t)| : ℂ)) i‖ ^ 2 with hc
  have hnorm : ∀ m : ℕ,
      ‖((-(1 / (2 * ((m:ℝ) + 1))) * (1 - (-1) ^ (m + 1)) : ℝ) : ℂ)‖ ^ 2 =
      (1 / (2 * ((m:ℝ) + 1))) ^ 2 * (1 - (-1) ^ (m + 1)) ^ 2 := by
    intro m
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  have hposc : ∀ m : ℕ, c ((m : ℤ) + 1) =
      (1 / (2 * ((m:ℝ) + 1))) ^ 2 * (1 - (-1) ^ (m + 1)) ^ 2 := by
    intro m
    rw [hc]
    simp only
    rw [fourierCoeffOn_log_abs_tan_pos m, hnorm m]
  have hnegc : ∀ m : ℕ, c (-((m : ℤ) + 1)) =
      (1 / (2 * ((m:ℝ) + 1))) ^ 2 * (1 - (-1) ^ (m + 1)) ^ 2 := by
    intro m
    rw [hc]
    simp only
    rw [fourierCoeffOn_log_abs_tan_neg m, hnorm m]
  have hzeroc : c 0 = 0 := by
    rw [hc]
    simp only
    rw [fourierCoeffOn_log_abs_tan_zero]
    simp
  -- the ℕ-half sums by parity
  have hhalf_val : HasSum (fun m : ℕ =>
      (1 / (2 * ((m:ℝ) + 1))) ^ 2 * (1 - (-1) ^ (m + 1)) ^ 2)
      (π ^ 2 / 8) := by
    have hE : ∀ k : ℕ, (fun m : ℕ =>
        (1 / (2 * ((m:ℝ) + 1))) ^ 2 * (1 - (-1) ^ (m + 1)) ^ 2) (2 * k) =
        (1:ℝ) / (2 * (k : ℝ) + 1) ^ 2 := by
      intro k
      simp only
      have hodd : ((-1:ℝ)) ^ (2 * k + 1) = -1 :=
        Odd.neg_one_pow ⟨k, by ring⟩
      rw [hodd]
      push_cast
      field_simp
      ring
    have hO : ∀ k : ℕ, (fun m : ℕ =>
        (1 / (2 * ((m:ℝ) + 1))) ^ 2 * (1 - (-1) ^ (m + 1)) ^ 2)
        (2 * k + 1) = 0 := by
      intro k
      simp only
      have heven : ((-1:ℝ)) ^ (2 * k + 1 + 1) = 1 :=
        Even.neg_one_pow ⟨k + 1, by ring⟩
      rw [heven]
      ring
    have he : HasSum (fun k : ℕ => (fun m : ℕ =>
        (1 / (2 * ((m:ℝ) + 1))) ^ 2 * (1 - (-1) ^ (m + 1)) ^ 2)
        (2 * k)) (π ^ 2 / 8) := by
      have hfun : (fun k : ℕ => (fun m : ℕ =>
          (1 / (2 * ((m:ℝ) + 1))) ^ 2 * (1 - (-1) ^ (m + 1)) ^ 2)
          (2 * k)) = fun k : ℕ => (1:ℝ) / (2 * (k : ℝ) + 1) ^ 2 :=
        funext hE
      rw [hfun]
      exact hasSum_odd_sq_inv
    have hoz : HasSum (fun k : ℕ => (fun m : ℕ =>
        (1 / (2 * ((m:ℝ) + 1))) ^ 2 * (1 - (-1) ^ (m + 1)) ^ 2)
        (2 * k + 1)) 0 := by
      have hfun : (fun k : ℕ => (fun m : ℕ =>
          (1 / (2 * ((m:ℝ) + 1))) ^ 2 * (1 - (-1) ^ (m + 1)) ^ 2)
          (2 * k + 1)) = fun _ : ℕ => (0:ℝ) := funext hO
      rw [hfun]
      exact hasSum_zero
    have h := HasSum.even_add_odd (f := fun m : ℕ =>
      (1 / (2 * ((m:ℝ) + 1))) ^ 2 * (1 - (-1) ^ (m + 1)) ^ 2) he hoz
    rw [add_zero] at h
    exact h
  have hhalf : HasSum (fun n : ℕ => c ((n : ℤ) + 1)) (π ^ 2 / 8) := by
    have heq : (fun m : ℕ =>
        (1 / (2 * ((m:ℝ) + 1))) ^ 2 * (1 - (-1) ^ (m + 1)) ^ 2) =
        fun n : ℕ => c ((n : ℤ) + 1) := by
      funext n
      rw [hposc n]
    rw [heq] at hhalf_val
    exact hhalf_val
  have hhalf' : HasSum (fun n : ℕ => c (-((n : ℤ) + 1))) (π ^ 2 / 8) := by
    have hagain : HasSum (fun m : ℕ =>
        (1 / (2 * ((m:ℝ) + 1))) ^ 2 * (1 - (-1) ^ (m + 1)) ^ 2)
        (π ^ 2 / 8) := by
      have heq : (fun m : ℕ =>
          (1 / (2 * ((m:ℝ) + 1))) ^ 2 * (1 - (-1) ^ (m + 1)) ^ 2) =
          fun n : ℕ => c ((n : ℤ) + 1) := by
        funext n
        rw [hposc n]
      rw [heq]
      exact hhalf
    have heq' : (fun m : ℕ =>
        (1 / (2 * ((m:ℝ) + 1))) ^ 2 * (1 - (-1) ^ (m + 1)) ^ 2) =
        fun n : ℕ => c (-((n : ℤ) + 1)) := by
      funext n
      rw [hnegc n]
    rw [heq'] at hagain
    exact hagain
  have hsum : HasSum c (π ^ 2 / 8 + c 0 + π ^ 2 / 8) :=
    HasSum.of_add_one_of_neg_add_one hhalf hhalf'
  have htsum : ∑' i : ℤ, c i = π ^ 2 / 4 := by
    rw [hsum.tsum_eq, hzeroc]
    ring
  rw [htsum] at hpars
  have hnorm2 : ∀ x : ℝ,
      ‖((Real.log |Real.tan (π * x)| : ℝ) : ℂ)‖ ^ 2 =
      Real.log |Real.tan (π * x)| ^ 2 := by
    intro x
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hcongr : ∫ x in (0:ℝ)..1,
      ‖((Real.log |Real.tan (π * x)| : ℝ) : ℂ)‖ ^ 2 =
      ∫ x in (0:ℝ)..1, Real.log |Real.tan (π * x)| ^ 2 :=
    intervalIntegral.integral_congr fun x _ => hnorm2 x
  rw [hcongr] at hpars
  have hsmul : ((1:ℝ) - 0)⁻¹ •
      (∫ x in (0:ℝ)..1, Real.log |Real.tan (π * x)| ^ 2) =
      ∫ x in (0:ℝ)..1, Real.log |Real.tan (π * x)| ^ 2 := by
    norm_num
  rw [hsmul] at hpars
  linarith [hpars]

end Fabius
