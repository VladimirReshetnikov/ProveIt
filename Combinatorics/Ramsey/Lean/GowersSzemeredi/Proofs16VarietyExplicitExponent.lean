import GowersSzemeredi.Proofs16VarietySampleBudget
import GowersSzemeredi.Proofs16CubicCapBound

/-! Explicit lower bounds for polynomial variety-family lifting. The sample
ceiling and rounded threshold disappear from the lower bound. All unknown
structure constants remain parameters; no printed numerical budget is asserted.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section16_polynomial_line_exponent_two (p q : Nat) (sigma theta gamma E : Real) :
    section16PolynomialLemma9Exponent 2 p q sigma theta gamma E =
      (multipleC (sigma / (2 * section16Lemma9R theta gamma 2)) gamma 3) ^
        section16Lemma9R theta gamma 2 * E / (8 * (p : Real) * ((q : Real) + 1)^16) := by
  unfold section16PolynomialLemma9Exponent
  norm_num only [Nat.reduceAdd, Nat.reducePow, Nat.reduceMul, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat]
  congr 1
  ring

/-- The all-box exponent has a ceiling-free lower bound with inner-loss
factor `sigma^17` and line factor `u^18`, before the fixed spectrum losses. -/
theorem section16_variety_capped_exponent_lower (Cv D Q q : Nat) {p pv : Nat}
    (hCv : 2 ≤ Cv) (hp : 0 < p) (hpv : 0 < pv) {c theta gamma sigma E z : Real}
    (hc : 0 < c) (hc1 : c ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hs : 0 < sigma) (hs1 : sigma ≤ 1) (hE : 0 < E) (hE1 : E ≤ 1)
    (hz : 0 < z) (hz1 : z ≤ 1) :
    let r := section16Lemma9R (theta / 2) gamma 2
    let u := (multipleC (sigma / (2 * r)) gamma 3)^r
    let e := section16PolynomialLemma9Exponent 2 p q sigma (theta / 2) gamma E
    let a := section16PolynomialJointVarietyExponent Cv pv
      (section16UniformSampleCount sigma (theta / 2) gamma 2 * Q) D c
    (u * E / (8 * (p : Real) * ((q : Real) + 1)^16)) *
      ((sigma * u)^17 /
        (1024 * (pv : Real)^2 * (4 * Cv + 18) * (milicevicBound D c + 2)^17 *
          (7^17 * ((Q : Real) + 1)^17))) / (16 + 4 * Real.log (16 / z)) ≤
      section16CappedWidthExponent (e * a / 4) (section16RoundedPowerThreshold z e a) := by
  intro r u e a
  obtain ⟨hu, hu1, hm⟩ := section16_variety_sampling_controls ht ht1 hg hg1 hs hs1
  have heq : e = u * E / (8 * (p : Real) * ((q : Real) + 1)^16) :=
    section16_polynomial_line_exponent_two p q sigma (theta / 2) gamma E
  have he : 0 < e := by
    rw [heq]
    exact div_pos (mul_pos hu hE) (by positivity)
  have he1 : e ≤ 1 := by
    rw [heq]
    apply (div_le_one (by positivity)).mpr
    have hn : u * E ≤ 1 := mul_le_one₀ hu1 hE.le hE1
    have hp1 : (1 : Real) ≤ p := by exact_mod_cast hp
    have hq1 : (1 : Real) ≤ ((q : Real) + 1)^16 := one_le_pow₀ (by have := Nat.cast_nonneg (α := Real) q; linarith)
    exact hn.trans (one_le_mul_of_one_le_of_one_le (by nlinarith only [hp1]) hq1)
  have ha := section16PolynomialJointVarietyExponent_pos Cv
    (section16UniformSampleCount sigma (theta / 2) gamma 2 * Q) D hpv hc hc1
  have ha1 := section16PolynomialJointVarietyExponent_le_one hCv hpv
    (section16UniformSampleCount sigma (theta / 2) gamma 2 * Q) D hc hc1
  have hlower := section16_variety_scalar_slice_lower Cv D _ Q hpv hc hc1 hs hs1 hu hu1 hm
  have hlog : 0 ≤ Real.log (16 / z) := Real.log_nonneg ((one_le_div hz).mpr (by linarith))
  apply le_trans _ (section16_cubic_capped_exponent_lower hz hz1 he he1 ha ha1)
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [← heq]
  exact mul_le_mul_of_nonneg_left hlower he.le

/-- Apply the explicit bound to the actual common-base controls when the
spectrum count and exponent are independent of the inner loss. -/
theorem section16_variety_lift_exponent_lower (C Cv D Q q : Nat) {p pv : Nat}
    (hC : 2 ≤ C) (hCv : 2 ≤ Cv) (hp : 0 < p) (hpv : 0 < pv)
    {c theta gamma sigma E : Real} (hc : 0 < c) (hc1 : c ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hs : 0 < sigma) (hs1 : sigma ≤ 1) (hE : 0 < E) (hE1 : E ≤ 1) :
    let r := section16Lemma9R (theta / 2) gamma 2
    let u := (multipleC (sigma / (2 * r)) gamma 3)^r
    let z := section16Zeta (theta / 2) gamma 2 /
      (4 * ((C * (q + 1) : Nat) : Real))
    (u * E / (8 * (p : Real) * ((q : Real) + 1)^16)) *
      ((sigma * u)^17 /
        (1024 * (pv : Real)^2 * (4 * Cv + 18) * (milicevicBound D c + 2)^17 *
          (7^17 * ((Q : Real) + 1)^17))) / (16 + 4 * Real.log (16 / z)) ≤
      section16CappedWidthExponent
        (section16PolynomialVarietyLiftExponent p Cv pv D Q c (theta / 2) gamma
          (fun _ => (q : Real)) (fun _ => E) (4 * sigma))
        (section16PolynomialVarietyLiftThreshold C p Cv pv D Q c (theta / 2) gamma
          (fun _ => (q : Real)) (fun _ => E) (4 * sigma)) := by
  intro r u z
  obtain ⟨hZ, hZ1⟩ := section16Zeta_pos_le_half 2
    (by positivity : 0 < theta / 2) (by linarith : theta / 2 ≤ 1) hg hg1
  have hCpos : 0 < C := by omega
  have hz : 0 < z := div_pos hZ (by positivity)
  have hz1 : z ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    have hsize : (1 : Real) ≤ ((C * (q + 1) : Nat) : Real) := by
      exact_mod_cast (show 1 ≤ C * (q + 1) by nlinarith)
    linarith
  have h := section16_variety_capped_exponent_lower Cv D Q q hCv hp hpv
    hc hc1 ht ht1 hg hg1 hs hs1 hE hE1 hz hz1
  simpa only [section16PolynomialVarietyLiftExponent, section16PolynomialVarietyLiftThreshold,
    Nat.floor_natCast, show 4 * sigma / 4 = sigma by ring] using h

end LeanProofs.GowersSzemeredi
