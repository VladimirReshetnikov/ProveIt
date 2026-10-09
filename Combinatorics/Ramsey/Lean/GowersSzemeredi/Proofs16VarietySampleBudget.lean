import GowersSzemeredi.Proofs16PolynomialVarietyCommonBaseCover
import GowersSzemeredi.Proofs16PartJBudget
import GowersSzemeredi.Proofs16CubicSampleBudget

/-! Remove the sample ceiling from the variety-family controls. The
remaining dependence is polynomial in the reciprocal line exponent and
the reciprocal inner loss, with all structure constants retained.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section16_variety_sampling_controls {theta gamma sigma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hs : 0 < sigma) (hs1 : sigma ≤ 1) :
    let r := section16Lemma9R (theta / 2) gamma 2
    let u := (multipleC (sigma / (2 * r)) gamma 3)^r
    0 < u ∧ u ≤ 1 ∧
      (section16UniformSampleCount sigma (theta / 2) gamma 2 : Real) ≤ 7 / (sigma * u) := by
  intro r u
  have hr1 : 1 ≤ r := partJ_lemma9R_one_le ht ht1 hg hg1
  have hr : 0 < r := zero_lt_one.trans_le hr1
  have hC : 0 < multipleC (sigma / (2 * r)) gamma 3 := multipleC_pos 3 (by positivity) hg
  have hC1 : multipleC (sigma / (2 * r)) gamma 3 ≤ 1 := by
    apply pow_le_one₀ (by positivity)
    have hsmall : sigma / (2 * r) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    exact mul_le_one₀ hg1 (by positivity) hsmall
  have hu : 0 < u := Real.rpow_pos_of_pos hC r
  have hu1 : u ≤ 1 := Real.rpow_le_one hC.le hC1 hr.le
  have hQi : section16Lemma9QBound sigma (theta / 2) gamma 2 = u⁻¹ := by
    simp only [section16Lemma9QBound, multipleQ, Real.inv_rpow hC.le, u, r]
  refine ⟨hu, hu1, ?_⟩
  have h := section16UniformSampleCount_le_seven hs hs1
    (by rw [hQi]; exact (one_le_inv₀ hu).mpr hu1)
  rw [hQi] at h
  convert h using 1 <;> ring

/-- A scalar ceiling-free lower bound for the joint slice exponent. -/
theorem section16_variety_scalar_slice_lower (Cv D m Q : Nat) {pv : Nat}
    (hpv : 0 < pv) {c sigma u : Real} (hc : 0 < c) (hc1 : c ≤ 1)
    (hs : 0 < sigma) (hs1 : sigma ≤ 1) (hu : 0 < u) (hu1 : u ≤ 1)
    (hm : (m : Real) ≤ 7 / (sigma * u)) :
    (sigma * u)^17 /
      (1024 * (pv : Real)^2 * (4 * Cv + 18) * (milicevicBound D c + 2)^17 *
        (7^17 * ((Q : Real) + 1)^17)) ≤
      section16PolynomialJointVarietyExponent Cv pv (m * Q) D c := by
  have hbase := two_le_milicevic_base hc hc1
  have hB : 0 ≤ milicevicBound D c := pow_nonneg (by linarith) D
  have hsu : 0 < sigma * u := mul_pos hs hu
  have hsu1 : sigma * u ≤ 1 := mul_le_one₀ hs1 hu.le hu1
  have hm' : (m : Real) * (sigma * u) ≤ 7 := (le_div_iff₀ hsu).mp hm
  have hmq : (sigma * u) * (((m * Q : Nat) : Real) + 1) ≤ 7 * ((Q : Real) + 1) := by
    have h := mul_le_mul_of_nonneg_right hm' (Nat.cast_nonneg Q : (0 : Real) ≤ Q)
    push_cast
    nlinarith only [h, hsu1]
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (sigma * u) * (((m * Q : Nat) : Real) + 1)) hmq 17
  rw [mul_pow, mul_pow (7 : Real) ((Q : Real) + 1) 17] at hpow
  unfold section16PolynomialJointVarietyExponent
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have h := mul_le_mul_of_nonneg_left hpow
    (by positivity : 0 ≤ 1024 * (pv : Real)^2 * (4 * Cv + 18) * (milicevicBound D c + 2)^17)
  convert h using 1 <;> simp only [one_mul, mul_assoc, mul_left_comm, mul_comm]

/-- Both controls have explicit polynomial bounds with no sample ceiling. -/
theorem section16_variety_sample_budget (Cv D Q : Nat) {pv : Nat} (hpv : 0 < pv)
    {c theta gamma sigma : Real} (hc : 0 < c) (hc1 : c ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hs : 0 < sigma) (hs1 : sigma ≤ 1) :
    let r := section16Lemma9R (theta / 2) gamma 2
    let u := (multipleC (sigma / (2 * r)) gamma 3)^r
    section16VarietyLiftGraphBound Q (theta / 2) gamma (4 * sigma) ≤
      81 * (7 / (sigma * u))^4 * (Q : Real)^2 ∧
    (sigma * u)^17 /
      (1024 * (pv : Real)^2 * (4 * Cv + 18) * (milicevicBound D c + 2)^17 *
        (7^17 * ((Q : Real) + 1)^17)) ≤
      section16PolynomialJointVarietyExponent Cv pv
        (section16UniformSampleCount sigma (theta / 2) gamma 2 * Q) D c := by
  intro r u
  obtain ⟨hu, hu1, hm⟩ := section16_variety_sampling_controls ht ht1 hg hg1 hs hs1
  constructor
  · unfold section16VarietyLiftGraphBound
    rw [show 4 * sigma / 4 = sigma by ring]
    gcongr
  · exact section16_variety_scalar_slice_lower Cv D _ Q hpv hc hc1 hs hs1 hu hu1 hm

end LeanProofs.GowersSzemeredi
