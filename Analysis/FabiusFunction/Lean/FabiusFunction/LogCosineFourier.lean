import FabiusFunction.CocycleParseval

/-!
# Fourier pairings of the cosine cocycle and the Gordin observable

The half-period shift `log (2 cos πt) = ψ(t + 1/2)` transports the
complete Fourier data of `ψ = log (2 sin π·)` to the cosine cocycle —
each coefficient picks up the alternating sign `(−1)^m` — and then, by
`log |tan π·| = log (2 sin π·) − log (2 cos π·)` almost everywhere, to
the Gordin observable:

`d-cos-pairing(m) = −(1 − (−1)^m)/(2m)` (`= −1/m` for odd `m`, `0`
for even), `d-sin-pairing(m) = 0`.

* `periodic_log_two_sin_pi_mul` — `1`-periodicity of `ψ`.
* `intervalIntegrable_sq_log_two_cos_pi_mul` — `(log 2 cos πt)² ∈ L¹`.
* `intervalIntegrable_log_two_cos_mul` — pairings of the cosine
  cocycle against bounded continuous detectors.
* `integral_log_two_cos_mul_cos`, `…_mul_sin` — the shifted pairings.
* `integral_log_abs_tan_mul_cos`, `…_mul_sin` — **the Gordin
  pairings**.
-/

set_option autoImplicit false

open Filter Topology intervalIntegral Real MeasureTheory

namespace Fabius

/-- The cocycle `ψ = log (2 sin π·)` is `1`-periodic. -/
theorem periodic_log_two_sin_pi_mul :
    Function.Periodic (fun t => Real.log (2 * Real.sin (π * t))) 1 := by
  intro t
  show Real.log (2 * Real.sin (π * (t + 1))) =
    Real.log (2 * Real.sin (π * t))
  rw [show π * (t + 1) = π * t + π by ring, Real.sin_add_pi, mul_neg,
    Real.log_neg_eq_log]

/-- `(log (2 cos πt))²` is interval integrable on `[0,1]`. -/
theorem intervalIntegrable_sq_log_two_cos_pi_mul :
    IntervalIntegrable (fun t => Real.log (2 * Real.cos (π * t)) ^ 2)
      MeasureTheory.volume 0 1 := by
  have hdom : IntervalIntegrable
      (fun t : ℝ => 2 * Real.log 2 ^ 2 +
        2 * Real.log (Real.cos (π * t)) ^ 2)
      MeasureTheory.volume 0 1 :=
    intervalIntegrable_const.add
      (intervalIntegrable_sq_log_cos_pi_mul.const_mul 2)
  apply hdom.mono_fun
  · exact ((Real.measurable_log.comp
      ((Real.measurable_cos.comp
        (measurable_const_mul π)).const_mul 2)).pow_const
      2).aestronglyMeasurable
  · have hhalf : ∀ᵐ t : ℝ, t ≠ (1 / 2 : ℝ) := by
      rw [MeasureTheory.ae_iff]
      simp
    have h1ae : ∀ᵐ t : ℝ, t ≠ (1 : ℝ) := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [MeasureTheory.ae_restrict_of_ae hhalf,
      MeasureTheory.ae_restrict_of_ae h1ae,
      MeasureTheory.ae_restrict_mem measurableSet_uIoc]
      with t hthalf ht1 hmem
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hmem
    have htpos : 0 < t := hmem.1
    have htlt : t < 1 := lt_of_le_of_ne hmem.2 ht1
    have hc : Real.cos (π * t) ≠ 0 := by
      intro hc0
      obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp hc0
      have hcan : π * t = π * ((2 * (k:ℝ) + 1) / 2) := by
        linear_combination hk
      have ht : t = (2 * (k:ℝ) + 1) / 2 :=
        mul_left_cancel₀ Real.pi_ne_zero hcan
      have hk0 : (0:ℝ) < 2 * (k:ℝ) + 1 := by
        rw [ht] at htpos
        linarith
      have hk2 : (2 * (k:ℝ) + 1) < 2 := by
        rw [ht] at htlt
        linarith
      have hk0' : (0:ℤ) < 2 * k + 1 := by exact_mod_cast hk0
      have hk2' : (2 * k + 1 : ℤ) < 2 := by exact_mod_cast hk2
      have hkz : k = 0 := by omega
      rw [hkz] at ht
      norm_num at ht
      exact hthalf ht
    have hsplit : Real.log (2 * Real.cos (π * t)) =
        Real.log 2 + Real.log (Real.cos (π * t)) :=
      Real.log_mul two_ne_zero hc
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.log 2 ^ 2 +
        2 * Real.log (Real.cos (π * t)) ^ 2), hsplit]
    nlinarith [sq_nonneg (Real.log 2 - Real.log (Real.cos (π * t)))]

/-- The cosine cocycle paired with any bounded continuous detector is
integrable. -/
theorem intervalIntegrable_log_two_cos_mul (g : ℝ → ℝ)
    (hg : Continuous g) (hb : ∀ x, |g x| ≤ 1) :
    IntervalIntegrable (fun t => Real.log (2 * Real.cos (π * t)) * g t)
      MeasureTheory.volume 0 1 := by
  have hdom : IntervalIntegrable
      (fun t => (1 + Real.log (2 * Real.cos (π * t)) ^ 2) / 2)
      MeasureTheory.volume 0 1 :=
    (intervalIntegrable_const.add
      intervalIntegrable_sq_log_two_cos_pi_mul).div_const 2
  apply hdom.mono_fun
  · exact ((Real.measurable_log.comp
      ((Real.measurable_cos.comp
        (measurable_const_mul π)).const_mul 2)).mul
      hg.measurable).aestronglyMeasurable
  · filter_upwards with t
    set A := Real.log (2 * Real.cos (π * t))
    simp only [Real.norm_eq_abs]
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 + A ^ 2) / 2)]
    have hA : |A| ≤ (1 + A ^ 2) / 2 := by
      nlinarith [sq_nonneg (|A| - 1), sq_abs A, abs_nonneg A]
    calc |A| * |g t| ≤ |A| * 1 :=
          mul_le_mul_of_nonneg_left (hb t) (abs_nonneg _)
      _ = |A| := mul_one _
      _ ≤ (1 + A ^ 2) / 2 := hA

/-- **The shifted cosine pairing**:
`∫₀¹ log (2 cos πt)·cos (2(m+1)πt) dt = (−1)^{m+1}·(−1/(2(m+1)))`. -/
theorem integral_log_two_cos_mul_cos (m : ℕ) :
    ∫ t in (0:ℝ)..1, Real.log (2 * Real.cos (π * t)) *
      Real.cos (2 * (m + 1) * (π * t)) =
      (-1) ^ (m + 1) * (-(1 / (2 * (m + 1)))) := by
  set G : ℝ → ℝ := fun u => Real.log (2 * Real.sin (π * u)) *
    Real.cos (2 * (m + 1) * (π * u)) with hG
  have hper : Function.Periodic G 1 := by
    intro u
    show Real.log (2 * Real.sin (π * (u + 1))) *
      Real.cos (2 * (m + 1) * (π * (u + 1))) =
      Real.log (2 * Real.sin (π * u)) *
        Real.cos (2 * (m + 1) * (π * u))
    have h2 : Real.cos (2 * ((m:ℝ) + 1) * (π * (u + 1))) =
        Real.cos (2 * ((m:ℝ) + 1) * (π * u)) := by
      have harg : 2 * ((m:ℝ) + 1) * (π * (u + 1)) =
          2 * ((m:ℝ) + 1) * (π * u) + ((m : ℤ) + 1 : ℤ) * (2 * π) := by
        push_cast
        ring
      rw [harg, Real.cos_add_int_mul_two_pi]
    rw [h2]
    exact congrArg (fun z => z * Real.cos (2 * ((m:ℝ) + 1) * (π * u)))
      (periodic_log_two_sin_pi_mul u)
  have hpt : ∀ t : ℝ, Real.log (2 * Real.cos (π * t)) *
      Real.cos (2 * (m + 1) * (π * t)) =
      (-1) ^ (m + 1) * G (t + 1 / 2) := by
    intro t
    show Real.log (2 * Real.cos (π * t)) *
      Real.cos (2 * (m + 1) * (π * t)) =
      (-1) ^ (m + 1) * (Real.log (2 * Real.sin (π * (t + 1 / 2))) *
        Real.cos (2 * (m + 1) * (π * (t + 1 / 2))))
    have h1 : Real.sin (π * (t + 1 / 2)) = Real.cos (π * t) := by
      rw [show π * (t + 1 / 2) = π * t + π / 2 by ring,
        Real.sin_add_pi_div_two]
    have h2 : Real.cos (2 * ((m:ℝ) + 1) * (π * (t + 1 / 2))) =
        (-1) ^ (m + 1) * Real.cos (2 * ((m:ℝ) + 1) * (π * t)) := by
      have harg : 2 * ((m:ℝ) + 1) * (π * (t + 1 / 2)) =
          2 * ((m:ℝ) + 1) * (π * t) + ((m + 1 : ℕ) : ℝ) * π := by
        push_cast
        ring
      rw [harg, Real.cos_add, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi]
      ring
    rw [h1, h2]
    have hsq : ((-1:ℝ)) ^ (m + 1) * (-1:ℝ) ^ (m + 1) = 1 := by
      rw [← pow_add]
      exact Even.neg_one_pow ⟨m + 1, by ring⟩
    linear_combination (-(Real.log (2 * Real.cos (π * t)) *
      Real.cos (2 * ((m:ℝ) + 1) * (π * t)))) * hsq
  calc ∫ t in (0:ℝ)..1, Real.log (2 * Real.cos (π * t)) *
      Real.cos (2 * (m + 1) * (π * t))
      = ∫ t in (0:ℝ)..1, (-1) ^ (m + 1) * G (t + 1 / 2) :=
        intervalIntegral.integral_congr fun t _ => hpt t
    _ = (-1) ^ (m + 1) * ∫ t in (0:ℝ)..1, G (t + 1 / 2) :=
        intervalIntegral.integral_const_mul _ _
    _ = (-1) ^ (m + 1) * ∫ u in (0 + 1 / 2 : ℝ)..(1 + 1 / 2 : ℝ), G u := by
        rw [intervalIntegral.integral_comp_add_right (f := G) (1 / 2)]
    _ = (-1) ^ (m + 1) * ∫ u in (1 / 2 : ℝ)..(1 / 2 + 1 : ℝ), G u := by
        norm_num
    _ = (-1) ^ (m + 1) * ∫ u in (0 : ℝ)..(0 + 1 : ℝ), G u := by
        rw [hper.intervalIntegral_add_eq (1 / 2) 0]
    _ = (-1) ^ (m + 1) * ∫ u in (0 : ℝ)..1, G u := by norm_num
    _ = (-1) ^ (m + 1) * (-(1 / (2 * (m + 1)))) :=
        congrArg (fun z => ((-1:ℝ)) ^ (m + 1) * z)
          (integral_log_two_sin_mul_cos m)

/-- **The shifted sine pairing vanishes**:
`∫₀¹ log (2 cos πt)·sin (2(m+1)πt) dt = 0`. -/
theorem integral_log_two_cos_mul_sin (m : ℕ) :
    ∫ t in (0:ℝ)..1, Real.log (2 * Real.cos (π * t)) *
      Real.sin (2 * (m + 1) * (π * t)) = 0 := by
  set G : ℝ → ℝ := fun u => Real.log (2 * Real.sin (π * u)) *
    Real.sin (2 * (m + 1) * (π * u)) with hG
  have hper : Function.Periodic G 1 := by
    intro u
    show Real.log (2 * Real.sin (π * (u + 1))) *
      Real.sin (2 * (m + 1) * (π * (u + 1))) =
      Real.log (2 * Real.sin (π * u)) *
        Real.sin (2 * (m + 1) * (π * u))
    have h2 : Real.sin (2 * ((m:ℝ) + 1) * (π * (u + 1))) =
        Real.sin (2 * ((m:ℝ) + 1) * (π * u)) := by
      have harg : 2 * ((m:ℝ) + 1) * (π * (u + 1)) =
          2 * ((m:ℝ) + 1) * (π * u) + ((m : ℤ) + 1 : ℤ) * (2 * π) := by
        push_cast
        ring
      rw [harg, Real.sin_add_int_mul_two_pi]
    rw [h2]
    exact congrArg (fun z => z * Real.sin (2 * ((m:ℝ) + 1) * (π * u)))
      (periodic_log_two_sin_pi_mul u)
  have hpt : ∀ t : ℝ, Real.log (2 * Real.cos (π * t)) *
      Real.sin (2 * (m + 1) * (π * t)) =
      (-1) ^ (m + 1) * G (t + 1 / 2) := by
    intro t
    show Real.log (2 * Real.cos (π * t)) *
      Real.sin (2 * (m + 1) * (π * t)) =
      (-1) ^ (m + 1) * (Real.log (2 * Real.sin (π * (t + 1 / 2))) *
        Real.sin (2 * (m + 1) * (π * (t + 1 / 2))))
    have h1 : Real.sin (π * (t + 1 / 2)) = Real.cos (π * t) := by
      rw [show π * (t + 1 / 2) = π * t + π / 2 by ring,
        Real.sin_add_pi_div_two]
    have h2 : Real.sin (2 * ((m:ℝ) + 1) * (π * (t + 1 / 2))) =
        (-1) ^ (m + 1) * Real.sin (2 * ((m:ℝ) + 1) * (π * t)) := by
      have harg : 2 * ((m:ℝ) + 1) * (π * (t + 1 / 2)) =
          2 * ((m:ℝ) + 1) * (π * t) + ((m + 1 : ℕ) : ℝ) * π := by
        push_cast
        ring
      rw [harg, Real.sin_add, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi]
      ring
    rw [h1, h2]
    have hsq : ((-1:ℝ)) ^ (m + 1) * (-1:ℝ) ^ (m + 1) = 1 := by
      rw [← pow_add]
      exact Even.neg_one_pow ⟨m + 1, by ring⟩
    linear_combination (-(Real.log (2 * Real.cos (π * t)) *
      Real.sin (2 * ((m:ℝ) + 1) * (π * t)))) * hsq
  calc ∫ t in (0:ℝ)..1, Real.log (2 * Real.cos (π * t)) *
      Real.sin (2 * (m + 1) * (π * t))
      = ∫ t in (0:ℝ)..1, (-1) ^ (m + 1) * G (t + 1 / 2) :=
        intervalIntegral.integral_congr fun t _ => hpt t
    _ = (-1) ^ (m + 1) * ∫ t in (0:ℝ)..1, G (t + 1 / 2) :=
        intervalIntegral.integral_const_mul _ _
    _ = (-1) ^ (m + 1) * ∫ u in (0 + 1 / 2 : ℝ)..(1 + 1 / 2 : ℝ), G u := by
        rw [intervalIntegral.integral_comp_add_right (f := G) (1 / 2)]
    _ = (-1) ^ (m + 1) * ∫ u in (1 / 2 : ℝ)..(1 / 2 + 1 : ℝ), G u := by
        norm_num
    _ = (-1) ^ (m + 1) * ∫ u in (0 : ℝ)..(0 + 1 : ℝ), G u := by
        rw [hper.intervalIntegral_add_eq (1 / 2) 0]
    _ = (-1) ^ (m + 1) * ∫ u in (0 : ℝ)..1, G u := by norm_num
    _ = 0 := by
        rw [show ∫ u in (0:ℝ)..1, G u = 0 from
          integral_log_two_sin_mul_sin m]
        ring

/-- **The Gordin cosine pairing**:
`∫₀¹ log |tan πt|·cos (2(m+1)πt) dt = −(1/(2(m+1)))·(1 − (−1)^{m+1})`
— `−1/(m+1)` at odd `m+1`, `0` at even. -/
theorem integral_log_abs_tan_mul_cos (m : ℕ) :
    ∫ t in (0:ℝ)..1, Real.log |Real.tan (π * t)| *
      Real.cos (2 * (m + 1) * (π * t)) =
      -(1 / (2 * (m + 1))) * (1 - (-1) ^ (m + 1)) := by
  have hsub : ∫ t in (0:ℝ)..1, Real.log |Real.tan (π * t)| *
      Real.cos (2 * (m + 1) * (π * t)) =
      ∫ t in (0:ℝ)..1, (Real.log (2 * Real.sin (π * t)) *
        Real.cos (2 * (m + 1) * (π * t)) -
        Real.log (2 * Real.cos (π * t)) *
          Real.cos (2 * (m + 1) * (π * t))) := by
    apply intervalIntegral.integral_congr_ae
    have hhalf : ∀ᵐ t : ℝ, t ≠ (1 / 2 : ℝ) := by
      rw [MeasureTheory.ae_iff]
      simp
    have h1ae : ∀ᵐ t : ℝ, t ≠ (1 : ℝ) := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [hhalf, h1ae] with t hthalf ht1 hmem
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hmem
    have htpos : 0 < t := hmem.1
    have htlt : t < 1 := lt_of_le_of_ne hmem.2 ht1
    have hs : 0 < Real.sin (π * t) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · positivity
      · nlinarith [Real.pi_pos]
    have hc : Real.cos (π * t) ≠ 0 := by
      intro hc0
      obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp hc0
      have hcan : π * t = π * ((2 * (k:ℝ) + 1) / 2) := by
        linear_combination hk
      have ht : t = (2 * (k:ℝ) + 1) / 2 :=
        mul_left_cancel₀ Real.pi_ne_zero hcan
      have hk0 : (0:ℝ) < 2 * (k:ℝ) + 1 := by
        rw [ht] at htpos
        linarith
      have hk2 : (2 * (k:ℝ) + 1) < 2 := by
        rw [ht] at htlt
        linarith
      have hk0' : (0:ℤ) < 2 * k + 1 := by exact_mod_cast hk0
      have hk2' : (2 * k + 1 : ℤ) < 2 := by exact_mod_cast hk2
      have hkz : k = 0 := by omega
      rw [hkz] at ht
      norm_num at ht
      exact hthalf ht
    have hkey : Real.log |Real.tan (π * t)| =
        Real.log (2 * Real.sin (π * t)) -
          Real.log (2 * Real.cos (π * t)) := by
      rw [Real.log_abs, Real.tan_eq_sin_div_cos,
        Real.log_div (ne_of_gt hs) hc,
        Real.log_mul two_ne_zero (ne_of_gt hs),
        Real.log_mul two_ne_zero hc]
      ring
    rw [hkey]
    ring
  rw [hsub, intervalIntegral.integral_sub
    (intervalIntegrable_log_two_sin_mul_cos m)
    (intervalIntegrable_log_two_cos_mul _ (by fun_prop)
      (fun x => Real.abs_cos_le_one _)),
    integral_log_two_sin_mul_cos m, integral_log_two_cos_mul_cos m]
  ring

/-- **The Gordin sine pairing vanishes**:
`∫₀¹ log |tan πt|·sin (2(m+1)πt) dt = 0`. -/
theorem integral_log_abs_tan_mul_sin (m : ℕ) :
    ∫ t in (0:ℝ)..1, Real.log |Real.tan (π * t)| *
      Real.sin (2 * (m + 1) * (π * t)) = 0 := by
  have hsub : ∫ t in (0:ℝ)..1, Real.log |Real.tan (π * t)| *
      Real.sin (2 * (m + 1) * (π * t)) =
      ∫ t in (0:ℝ)..1, (Real.log (2 * Real.sin (π * t)) *
        Real.sin (2 * (m + 1) * (π * t)) -
        Real.log (2 * Real.cos (π * t)) *
          Real.sin (2 * (m + 1) * (π * t))) := by
    apply intervalIntegral.integral_congr_ae
    have hhalf : ∀ᵐ t : ℝ, t ≠ (1 / 2 : ℝ) := by
      rw [MeasureTheory.ae_iff]
      simp
    have h1ae : ∀ᵐ t : ℝ, t ≠ (1 : ℝ) := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [hhalf, h1ae] with t hthalf ht1 hmem
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hmem
    have htpos : 0 < t := hmem.1
    have htlt : t < 1 := lt_of_le_of_ne hmem.2 ht1
    have hs : 0 < Real.sin (π * t) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · positivity
      · nlinarith [Real.pi_pos]
    have hc : Real.cos (π * t) ≠ 0 := by
      intro hc0
      obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp hc0
      have hcan : π * t = π * ((2 * (k:ℝ) + 1) / 2) := by
        linear_combination hk
      have ht : t = (2 * (k:ℝ) + 1) / 2 :=
        mul_left_cancel₀ Real.pi_ne_zero hcan
      have hk0 : (0:ℝ) < 2 * (k:ℝ) + 1 := by
        rw [ht] at htpos
        linarith
      have hk2 : (2 * (k:ℝ) + 1) < 2 := by
        rw [ht] at htlt
        linarith
      have hk0' : (0:ℤ) < 2 * k + 1 := by exact_mod_cast hk0
      have hk2' : (2 * k + 1 : ℤ) < 2 := by exact_mod_cast hk2
      have hkz : k = 0 := by omega
      rw [hkz] at ht
      norm_num at ht
      exact hthalf ht
    have hkey : Real.log |Real.tan (π * t)| =
        Real.log (2 * Real.sin (π * t)) -
          Real.log (2 * Real.cos (π * t)) := by
      rw [Real.log_abs, Real.tan_eq_sin_div_cos,
        Real.log_div (ne_of_gt hs) hc,
        Real.log_mul two_ne_zero (ne_of_gt hs),
        Real.log_mul two_ne_zero hc]
      ring
    rw [hkey]
    ring
  rw [hsub, intervalIntegral.integral_sub
    (intervalIntegrable_log_two_sin_mul_sin_pairing m)
    (intervalIntegrable_log_two_cos_mul _ (by fun_prop)
      (fun x => Real.abs_sin_le_one _)),
    integral_log_two_sin_mul_sin m, integral_log_two_cos_mul_sin m]
  ring

end Fabius
