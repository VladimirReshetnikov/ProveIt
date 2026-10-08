import GowersSzemeredi.Proofs16PartJBudget

/-! Part J: Theorem 16.2 and Corollary 16.11 in dimension three, conditionally.

This module completes the dimension-three budget comparison begun in
`Proofs16PartJBudget`. The steps are:

* the lift exponent of the dimension-three pieces, its power form (the
  capped exponent bounded below) and its algebraic form (divided by
  `10*s(theta/2,gamma,2)`);
* a width lower bound through `section16_cubic_scalar_width`, with the
  dimension-two recurrence `576^(-24 n) ≥ 2^(-240 n)`;
* power absorption at the piece parameter `s = U^9`;
* the source width `c(s⁻¹ rho, gamma, 3)^s ≤ algebraic exponent`, and the
  graph budget `graph bound × algebraic exponent ≤ 1`;
* the conversion of the cubic controls to the source's
  `MultiplyLinear gamma s`, and the piece budget
  `s ≤ mass * s(theta,gamma,3)`;
* `theorem_16_2_at_three_of_stackable` and
  `corollary_16_11_at_three_of_stackable`.

The two hypotheses are the stackable dimension-two structure, with
polynomial bounds on its counts (research notes, Part J). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

section Exponents

variable (Q q : Real → Real → Nat) (theta gamma rho : Real)

/-- The cubic lift exponent of the dimension-three pieces. -/
def partJLiftExponent : Real :=
  section16CubicLiftExponent (Q gamma (theta / 4) * q gamma (theta / 4)) 2 (rho / 4)
    (theta / 2) gamma
    (fun _ => ((3 * partJSpectrumCount Q q (theta / 2) gamma : Nat) : Real))
    (cubicBaseExponent (partJSpectrumCount Q q (theta / 2) gamma))

/-- The lift exponent divided by the logarithmic Bohr-radius denominator. -/
def partJPowerExponent : Real :=
  partJLiftExponent Q q theta gamma rho /
    (4 + Real.log (32 / section16Zeta (theta / 2) gamma 2))

/-- The lift exponent divided by the outer source scale. -/
def partJAlgebraicExponent : Real :=
  partJLiftExponent Q q theta gamma rho / (10 * multipleS (theta / 2) gamma 2)

end Exponents

variable {Q q : Real → Real → Nat} {theta gamma : Real}

theorem partJLiftExponent_pos (hQ : 0 < Q gamma (theta / 4)) (hq : 0 < q gamma (theta / 4))
    (hn : 0 < partJSpectrumCount Q q (theta / 2) gamma)
    (ht : 0 < theta) (hg : 0 < gamma) {rho : Real} (hr : 0 < rho) :
    0 < partJLiftExponent Q q theta gamma rho :=
  section16CubicLiftExponent_pos (Nat.mul_pos hQ hq) (by norm_num) (by positivity)
    (by positivity) hg (cubicBaseExponent_pos hn (by positivity))

theorem partJAlgebraicExponent_pos (hQ : 0 < Q gamma (theta / 4)) (hq : 0 < q gamma (theta / 4))
    (hn : 0 < partJSpectrumCount Q q (theta / 2) gamma)
    (ht : 0 < theta) (hg : 0 < gamma) {rho : Real} (hr : 0 < rho) :
    0 < partJAlgebraicExponent Q q theta gamma rho := by
  have hl := partJLiftExponent_pos hQ hq hn ht hg hr
  unfold partJAlgebraicExponent
  have hS : 0 < multipleS (theta / 2) gamma 2 := by unfold multipleS; positivity
  positivity

/-- The power exponent is at most the capped exponent of the pieces. -/
theorem partJPowerExponent_le (hQ : 0 < Q gamma (theta / 4)) (hq : 0 < q gamma (theta / 4))
    (hn : 0 < partJSpectrumCount Q q (theta / 2) gamma)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {rho : Real} (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    partJPowerExponent Q q theta gamma rho ≤ partJExponent Q q theta gamma rho := by
  have ht2 : 0 < theta / 2 := by positivity
  have ht21 : theta / 2 ≤ 1 := by linarith
  let n := partJSpectrumCount Q q (theta / 2) gamma
  let qq := Q gamma (theta / 4) * q gamma (theta / 4)
  let Qd := fun _ : Real => ((3 * n : Nat) : Real)
  let Ed := cubicBaseExponent n
  let e := lemma9WidthWithExponent ⌈Qd (rho / 4 / 2)⌉₊ 2 (rho / 4) (theta / 2) gamma (Ed (rho / 4 / 2))
  let a := cubicBaseExponent (section16UniformSampleCount (rho / 4) (theta / 2) gamma 2 * qq) (rho / 4)
  have hsample := Nat.mul_pos
    (section16UniformSampleCount_pos (theta := theta / 2) (gamma := gamma) 2
      (by positivity : 0 < rho / 4)) (Nat.mul_pos hQ hq)
  have hEd : 0 < Ed (rho / 4 / 2) := cubicBaseExponent_pos hn (by positivity)
  have hEd1 : Ed (rho / 4 / 2) ≤ 1 := cubicBaseExponent_le_one hn (by positivity) (by linarith)
  have he : 0 < e := lemma9WidthWithExponent_pos (by norm_num) (by positivity) ht2 hg hEd _
  have hR := partJ_lemma9R_one_le ht ht1 hg hg1
  have he1 : e ≤ 1 := lemma9WidthWithExponent_le_one (by positivity) (by linarith) hg hg1 hEd hEd1 hR
  have ha : 0 < a := cubicBaseExponent_pos hsample (by positivity)
  have ha1 : a ≤ 1 := cubicBaseExponent_le_one hsample (by positivity) (by linarith)
  obtain ⟨hz, hz1⟩ := section16Zeta_pos_le_half 2 ht2 ht21 hg hg1
  have hcap := section16_cubic_capped_exponent_lower
    (by positivity : 0 < section16Zeta (theta / 2) gamma 2 / 2) (by linarith) he he1 ha ha1
  have hratio : 16 / (section16Zeta (theta / 2) gamma 2 / 2) = 32 / section16Zeta (theta / 2) gamma 2 := by
    ring
  rw [hratio] at hcap
  convert hcap using 1
  · change (e * a / 4) / (4 + Real.log (32 / section16Zeta (theta / 2) gamma 2)) =
      e * a / (16 + 4 * Real.log (32 / section16Zeta (theta / 2) gamma 2))
    rw [div_div]
    congr 1
    ring
  · rfl

/-- The algebraic exponent is at most the power exponent. -/
theorem partJAlgebraicExponent_le (hQ : 0 < Q gamma (theta / 4)) (hq : 0 < q gamma (theta / 4))
    (hn : 0 < partJSpectrumCount Q q (theta / 2) gamma)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {rho : Real} (hrho : 0 < rho) :
    partJAlgebraicExponent Q q theta gamma rho ≤ partJPowerExponent Q q theta gamma rho := by
  have ht2 : 0 < theta / 2 := by positivity
  have ht21 : theta / 2 ≤ 1 := by linarith
  obtain ⟨hz, hz1⟩ := section16Zeta_pos_le_half 2 ht2 ht21 hg hg1
  have hlog : 0 ≤ Real.log (32 / section16Zeta (theta / 2) gamma 2) :=
    Real.log_nonneg ((one_le_div hz).mpr (by linarith))
  apply div_le_div_of_nonneg_left (partJLiftExponent_pos hQ hq hn ht hg hrho).le (by positivity)
  exact section16_cubic_outer_denominator_le 2 ht2 ht21 hg hg1

/-- The width lower bound in dimension three. -/
theorem partJ_width_lower_bound (hQb : PolyBoundedControl Q) (hqb : PolyBoundedControl q)
    (hQ : 0 < Q gamma (theta / 4)) (hq : 0 < q gamma (theta / 4))
    (hn : 0 < partJSpectrumCount Q q (theta / 2) gamma)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {sigma : Real} (hs : 0 < sigma) (hs1 : sigma ≤ 1) :
    let U := multipleS theta gamma 2
    let R := section16Lemma9R (theta / 2) gamma 2
    let u := (multipleC (sigma / (2 * R)) gamma 3)^R
    u^5 * sigma^10 * (2 : Real)^(-(240 * U^2 + 75)) / U^14 ≤
      partJAlgebraicExponent Q q theta gamma (4 * sigma) := by
  let U := multipleS theta gamma 2
  let R := section16Lemma9R (theta / 2) gamma 2
  let u := (multipleC (sigma / (2 * R)) gamma 3)^R
  let n := partJSpectrumCount Q q (theta / 2) gamma
  let qq := Q gamma (theta / 4) * q gamma (theta / 4)
  let M := section16UniformSampleCount sigma (theta / 2) gamma 2
  have hU16 := partJ_U_ge_sixteen ht ht1 hg hg1
  have hU : 0 < U := by linarith only [hU16]
  have hU1 : 1 ≤ U := by linarith only [hU16]
  have hR1 : 1 ≤ R := partJ_lemma9R_one_le ht ht1 hg hg1
  have hR : 0 < R := zero_lt_one.trans_le hR1
  have hC : 0 < multipleC (sigma / (2 * R)) gamma 3 := multipleC_pos 3 (by positivity) hg
  have hC1 : multipleC (sigma / (2 * R)) gamma 3 ≤ 1 := by
    unfold multipleC
    apply pow_le_one₀ (by positivity)
    have hsmall : sigma / (2 * R) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith only [hs1, hR1])
    exact mul_le_one₀ hg1 (by positivity) hsmall
  have hu : 0 < u := Real.rpow_pos_of_pos hC R
  have hu1 : u ≤ 1 := Real.rpow_le_one hC.le hC1 hR.le
  have hQi : section16Lemma9QBound sigma (theta / 2) gamma 2 = u⁻¹ := by
    simp only [section16Lemma9QBound, multipleQ, Real.inv_rpow hC.le, u, R]
  have hM : (0 : Real) < M := by
    exact_mod_cast section16UniformSampleCount_pos (theta := theta / 2) (gamma := gamma) 2 hs
  have hMs : (M : Real) ≤ 7 / (sigma * u) := by
    have hh := section16UniformSampleCount_le_seven (theta := theta / 2) (gamma := gamma)
      (k := 2) hs hs1 (by rw [hQi]; exact (one_le_inv₀ hu).mpr hu1)
    rw [hQi] at hh
    convert hh using 1; ring
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hqR : (0 : Real) < (qq : Real) := by exact_mod_cast Nat.mul_pos hQ hq
  have hV : 0 < multipleS (theta / 2) gamma 2 := by unfold multipleS; positivity
  have hnU : (n : Real) ≤ U := partJ_spectrum_scale_le hQb hqb ht ht1 hg hg1
  have hnU2 : (n : Real) ≤ U^2 := hnU.trans (by nlinarith only [hU1])
  have hqU : (qq : Real) ≤ U := partJ_slice_scale_le hQb hqb ht ht1 hg hg1
  have hscalar := section16_cubic_scalar_width hU hu hs hV hnR hM hqR
    (section16RecurrenceExponent_pos_le_one 2 (3 * n)).1.le
    (multipleS_half_le_square 2 ht ht1 hg hg1) hnU2 hqU hMs
  have hrec : (2 : Real)^(-(240 * U^2)) ≤ section16RecurrenceExponent 2 (3 * n) := by
    apply le_trans _ (partJ_recurrence_lower n)
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith only [hnU2]
  change u^5 * sigma^10 * (2 : Real)^(-(240 * U^2 + 75)) / U^14 ≤ _
  have hproduct : (2 : Real)^(-(240 * U^2 + 75)) =
      (2 : Real)^(-(75 : Real)) * (2 : Real)^(-(240 * U^2)) := by
    rw [← Real.rpow_add (by norm_num : (0 : Real) < 2)]
    congr 1
    ring
  calc
    _ ≤ (2 : Real)^(-(75 : Real)) * u^5 * sigma^10 *
        section16RecurrenceExponent 2 (3 * n) / U^14 := by
      rw [hproduct]
      have hc0 : 0 ≤ (2 : Real)^(-(75 : Real)) := by positivity
      have hh := mul_le_mul_of_nonneg_left hrec
        (mul_nonneg (mul_nonneg hc0 (pow_nonneg hu.le 5)) (pow_nonneg hs.le 10))
      apply div_le_div_of_nonneg_right _ (by positivity)
      convert hh using 1; ring
    _ ≤ _ := by
      convert hscalar using 1
      simp only [partJAlgebraicExponent, partJLiftExponent,
        show 4 * sigma / 4 = sigma by ring, section16CubicLiftExponent,
        lemma9WidthWithExponent, cubicBaseExponent, Nat.ceil_natCast]
      simp only [Nat.cast_mul, qq, M, n, u, R]
      try rfl

theorem partJ_exponent_reserve {U A R : Real}
    (hU : 16 ≤ U) (hA : 1 ≤ A) (hR : R ≤ U^8) :
    5 * A * R + 240 * U^2 + 99 ≤ A * U^9 := by
  have hU0 : 0 ≤ U := by linarith
  have hU1 : 1 ≤ U := by linarith
  have hU2 : (256 : Real) ≤ U^2 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 16) hU 2
    norm_num at hh
    exact hh
  have hp : U^2 ≤ U^8 := pow_le_pow_right₀ hU1 (by norm_num)
  have h9 : U^9 = U * U^8 := by ring
  have hU8 : 0 ≤ U^8 := by positivity
  have h4 : 256 * U^2 ≤ U^4 := by
    calc
      256 * U^2 ≤ U^2 * U^2 := mul_le_mul_of_nonneg_right hU2 (by positivity)
      _ = U^4 := by ring
  have h48 : U^4 ≤ U^8 := pow_le_pow_right₀ hU1 (by norm_num)
  have hres : 240 * U^2 + 99 ≤ 11 * U^8 := by linarith only [hU2, h4, h48]
  have hmain : 16 * U^8 ≤ U^9 := by rw [h9]; nlinarith only [hU, hU8]
  have hAR : 5 * A * R ≤ 5 * A * U^8 := by nlinarith only [hA, hR]
  have hA8 : 11 * U^8 ≤ 11 * A * U^8 := by nlinarith only [hA, hU8]
  have hfin : 16 * A * U^8 ≤ A * U^9 := by nlinarith only [hmain, hA]
  linarith only [hres, hAR, hA8, hfin]

theorem partJ_power_absorption_of_bounds {U A R p t sigma : Real}
    (hU : 16 ≤ U) (hA : 1 ≤ A) (hR : 0 < R) (hRU : R ≤ U^8)
    (hp : 0 < p) (hp1 : p ≤ 1) (hpt : p ≤ t) (hps : p ≤ sigma)
    (hp2 : p ≤ 1 / 2) (hpU : p ≤ U⁻¹) :
    p ^ (A * U^9) ≤ t ^ (5 * A * R) * sigma^(10 : Nat) *
      (2 : Real)^(-(240 * U^2 + 75)) / U^(14 : Nat) := by
  have ht0 : 0 ≤ t := hp.le.trans hpt
  have hs0 : 0 ≤ sigma := hp.le.trans hps
  have hA0 : 0 < A := by linarith
  have hreserve := partJ_exponent_reserve hU hA hRU
  have hfirst : p ^ (5 * A * R) ≤ t ^ (5 * A * R) :=
    Real.rpow_le_rpow hp.le hpt (by positivity)
  have hsecond : p^(10 : Nat) ≤ sigma^(10 : Nat) := pow_le_pow_left₀ hp.le hps _
  have hthird : p ^ (240 * U^2 + 75) ≤ (2 : Real)^(-(240 * U^2 + 75)) := by
    calc
      _ ≤ (1 / 2 : Real) ^ (240 * U^2 + 75) := Real.rpow_le_rpow hp.le hp2 (by positivity)
      _ = _ := by rw [one_div, ← Real.rpow_neg_eq_inv_rpow]
  have hfourth : p^(14 : Nat) ≤ (U^(14 : Nat))⁻¹ := by
    simpa only [inv_pow] using pow_le_pow_left₀ hp.le hpU 14
  calc
    p ^ (A * U^9) ≤ p ^ (5 * A * R + 10 + (240 * U^2 + 75) + 14) :=
      Real.rpow_le_rpow_of_exponent_ge hp hp1 (by linarith only [hreserve])
    _ = p ^ (5 * A * R) * p^(10 : Nat) * p ^ (240 * U^2 + 75) * p^(14 : Nat) := by
      simp only [Real.rpow_add hp, Real.rpow_ofNat]
    _ ≤ _ := by
      rw [div_eq_mul_inv]
      exact mul_le_mul
        (mul_le_mul (mul_le_mul hfirst hsecond (by positivity) (by positivity))
          hthird (by positivity) (by positivity)) hfourth (by positivity) (by positivity)

theorem partJ_power_absorption {U A R gamma sigma : Real}
    (hU : 16 ≤ U) (hA : 1 ≤ A) (hR : 0 < R) (hRU : R ≤ U^8)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hs : 0 < sigma) (hs1 : sigma ≤ 1) :
    (4 * gamma * sigma / U^9) ^ (A * U^9) ≤
      (gamma * sigma / (2 * R)) ^ (5 * A * R) * sigma^(10 : Nat) *
      (2 : Real)^(-(240 * U^2 + 75)) / U^(14 : Nat) := by
  have hU0 : 0 < U := by linarith
  have hU1 : 1 ≤ U := by linarith
  have hU8 : (16 : Real) ≤ U^8 := le_trans hU (le_self_pow₀ hU1 (by norm_num))
  have hU9 : 16 * U^8 ≤ U^9 := by
    have : U^9 = U * U^8 := by ring
    rw [this]; nlinarith only [hU, pow_nonneg hU0.le 8]
  have hprod : gamma * sigma ≤ 1 := mul_le_one₀ hg1 hs.le hs1
  have hp2 : 4 * gamma * sigma / U^9 ≤ (1 / 2 : Real) := by
    apply (div_le_iff₀ (pow_pos hU0 9)).mpr
    nlinarith only [hprod, hU8, hU9]
  apply partJ_power_absorption_of_bounds hU hA hR hRU (by positivity) (by linarith only [hp2]) ?_ ?_
    hp2 ?_
  · have hRscale : 8 * R ≤ U^9 := by nlinarith only [hRU, hU9, hU8]
    apply (div_le_div_iff₀ (pow_pos hU0 9) (by positivity : 0 < 2 * R)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hRscale (mul_pos hg hs).le]
  · apply (div_le_iff₀ (pow_pos hU0 9)).mpr
    nlinarith only [hs.le, mul_le_mul_of_nonneg_right hg1 hs.le,
      mul_le_mul_of_nonneg_right (hU8.trans (by nlinarith only [hU9, hU8] : U^8 ≤ U^9)) hs.le]
  · rw [← one_div]
    apply (div_le_div_iff₀ (pow_pos hU0 9) hU0).mpr
    have h8 : 4 ≤ U^8 := by linarith only [hU8]
    have h98 : U^9 = U^8 * U := by ring
    rw [h98]
    nlinarith only [mul_le_mul_of_nonneg_right hprod hU0.le,
      mul_le_mul_of_nonneg_right h8 hU0.le]

/-- **The source width in dimension three** at the piece parameter `U^9`. -/
theorem partJ_source_width (hQb : PolyBoundedControl Q) (hqb : PolyBoundedControl q)
    (hQ : 0 < Q gamma (theta / 4)) (hq : 0 < q gamma (theta / 4))
    (hn : 0 < partJSpectrumCount Q q (theta / 2) gamma)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {rho : Real} (hr : 0 < rho) (hr1 : rho ≤ 1) :
    (multipleC (((multipleS theta gamma 2)^9)⁻¹ * rho) gamma 3)^((multipleS theta gamma 2)^9) ≤
      partJAlgebraicExponent Q q theta gamma rho := by
  let U := multipleS theta gamma 2
  let R := section16Lemma9R (theta / 2) gamma 2
  let sigma := rho / 4
  let A : Real := ((2 : Nat)^((2 : Nat)^(3 + 8)) : Nat)
  let t := gamma * sigma / (2 * R)
  have hU16 := partJ_U_ge_sixteen ht ht1 hg hg1
  have hU : 0 < U := by linarith only [hU16]
  have hR1 : 1 ≤ R := partJ_lemma9R_one_le ht ht1 hg hg1
  have hR : 0 < R := zero_lt_one.trans_le hR1
  have hs : 0 < sigma := by dsimp [sigma]; positivity
  have hs1 : sigma ≤ 1 := by dsimp [sigma]; linarith only [hr1]
  have hA : 1 ≤ A := by
    change (1 : Real) ≤ ((2 : Nat)^((2 : Nat)^(3 + 8)) : Nat)
    exact_mod_cast (one_le_pow₀ (by decide : (1 : Nat) ≤ 2) (n := 2^(3 + 8)))
  have ht0 : 0 < t := by dsimp [t]; positivity
  have hC : multipleC (sigma / (2 * R)) gamma 3 = t^A := by
    unfold multipleC
    rw [show gamma * (sigma / (2 * R)) = t by dsimp [t]; ring]
    exact (Real.rpow_natCast _ _).symm
  have hpow : ((multipleC (sigma / (2 * R)) gamma 3)^R)^ (5 : Nat) = t^(5 * A * R) := by
    rw [hC, ← Real.rpow_mul ht0.le, ← Real.rpow_natCast,
      ← Real.rpow_mul ht0.le]
    exact congrArg (fun z : Real => t^z)
      ((mul_comm (A * R) 5).trans (mul_assoc 5 A R).symm)
  have hsource : (multipleC ((U^9)⁻¹ * rho) gamma 3)^(U^9) =
      (4 * gamma * sigma / U^9)^(A * U^9) := by
    have hb : gamma * ((U^9)⁻¹ * rho) = 4 * gamma * sigma / U^9 := by
      dsimp [sigma]
      ring
    unfold multipleC
    rw [hb, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  have habs := partJ_power_absorption hU16 hA hR (partJ_remainder_scale_le ht ht1 hg hg1)
    hg hg1 hs hs1
  have hlower := partJ_width_lower_bound hQb hqb hQ hq hn ht ht1 hg hg1 hs hs1
  change (multipleC ((U^9)⁻¹ * rho) gamma 3)^(U^9) ≤ _
  rw [hsource]
  apply habs.trans
  change ((multipleC (sigma / (2 * R)) gamma 3)^R)^5 * sigma^10 *
    (2 : Real)^(-(240 * U^2 + 75)) / U^14 ≤ _ at hlower
  rw [hpow] at hlower
  simpa only [show 4 * sigma = rho by dsimp [sigma]; ring] using hlower

/-- The graph count times the algebraic exponent is at most one. -/
theorem partJ_graph_width_budget (hQ : 0 < Q gamma (theta / 4)) (hq : 0 < q gamma (theta / 4))
    (hn : 0 < partJSpectrumCount Q q (theta / 2) gamma)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {rho : Real} (hr : 0 < rho) (hr1 : rho ≤ 1) :
    partJGraphBound Q q theta gamma rho * partJAlgebraicExponent Q q theta gamma rho ≤ 1 := by
  have ht2 : 0 < theta / 2 := by positivity
  have ht21 : theta / 2 ≤ 1 := by linarith
  let n := partJSpectrumCount Q q (theta / 2) gamma
  let qq := Q gamma (theta / 4) * q gamma (theta / 4)
  let M := section16UniformSampleCount (rho / 4) (theta / 2) gamma 2
  let Qd := fun _ : Real => ((3 * n : Nat) : Real)
  let Ed := cubicBaseExponent n
  let e := lemma9WidthWithExponent ⌈Qd (rho / 4 / 2)⌉₊ 2 (rho / 4) (theta / 2) gamma (Ed (rho / 4 / 2))
  have hEd : 0 < Ed (rho / 4 / 2) := cubicBaseExponent_pos hn (by positivity)
  have hEd1 : Ed (rho / 4 / 2) ≤ 1 := cubicBaseExponent_le_one hn (by positivity) (by linarith)
  have he : 0 < e := lemma9WidthWithExponent_pos (by norm_num) (by positivity) ht2 hg hEd _
  have hR := partJ_lemma9R_one_le ht ht1 hg hg1
  have he1 : e ≤ 1 := lemma9WidthWithExponent_le_one (by positivity) (by linarith) hg hg1 hEd hEd1 hR
  have hM : (0 : Real) < M := by
    exact_mod_cast section16UniformSampleCount_pos
      (theta := theta / 2) (gamma := gamma) 2 (by positivity : 0 < rho / 4)
  have hM1 : (1 : Real) ≤ M := by exact_mod_cast (show 1 ≤ M by exact_mod_cast hM)
  have hq1 : (1 : Real) ≤ (qq : Real) := by exact_mod_cast Nat.mul_pos hQ hq
  have hV := one_le_multipleS 2 ht2 ht21 hg hg1
  have hh := section16_cubic_scalar_graph_width hM hq1 hV
    (by positivity : 0 ≤ rho / 4) (by linarith : rho / 4 ≤ 1) he1
  have halg : partJAlgebraicExponent Q q theta gamma rho =
      (e * ((2 : Real)^(-(27 : Real)) * (rho / 4)^3 / ((M : Real) * (qq : Real))^4) / 4) /
        (10 * multipleS (theta / 2) gamma 2) := by
    simp only [partJAlgebraicExponent, partJLiftExponent, section16CubicLiftExponent,
      cubicBaseExponent, e, Qd, Ed, qq, M, n, Nat.cast_mul]
    try rfl
  have hpos := partJAlgebraicExponent_pos hQ hq hn ht hg hr
  have hsmall : 27 * partJAlgebraicExponent Q q theta gamma rho ≤ 1 := by
    rw [halg]
    have hc : (2 : Real)^(-(27 : Real)) ≤ 1 := by norm_num [Real.rpow_neg, Real.rpow_ofNat]
    have hfrac : (rho / 4)^3 / ((M : Real) * (qq : Real))^4 ≤ 1 := by
      apply div_le_one_of_le₀ _ (by positivity)
      have h1 : (rho / 4)^3 ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
      have h2 : (1 : Real) ≤ ((M : Real) * (qq : Real))^4 :=
        one_le_pow₀ (one_le_mul_of_one_le_of_one_le hM1 hq1)
      linarith only [h1, h2]
    have hinner : e * ((2 : Real)^(-(27 : Real)) * (rho / 4)^3 / ((M : Real) * (qq : Real))^4) ≤ 1 := by
      have hx : (2 : Real)^(-(27 : Real)) * (rho / 4)^3 / ((M : Real) * (qq : Real))^4 ≤ 1 := by
        rw [mul_div_assoc]
        exact mul_le_one₀ hc (by positivity) hfrac
      exact mul_le_one₀ he1 (by positivity) hx
    have hden : (10 : Real) ≤ 10 * multipleS (theta / 2) gamma 2 := by linarith only [hV]
    rw [div_div, mul_div_assoc']
    apply (div_le_one (by positivity)).mpr
    nlinarith only [hinner, hden, he.le]
  have hbig : 9 * (M : Real)^4 * (qq : Real)^2 * partJAlgebraicExponent Q q theta gamma rho ≤ 1 := by
    rw [halg]
    convert hh using 1
  unfold partJGraphBound section16CubicLiftGraphBound
  change max (9 * (M : Real)^4 * (qq : Real)^2) 27 * _ ≤ 1
  rw [max_mul_of_nonneg _ _ hpos.le]
  exact max_le hbig hsmall

/-- The dimension-three pieces satisfy the source's multiple linearity at
parameter `U^9`. -/
theorem MultiplyLinearWith.partJ_source_control {N : Nat} [NeZero N]
    {Gamma : Finset (Point N 3 × ZMod N)}
    (hQb : PolyBoundedControl Q) (hqb : PolyBoundedControl q)
    (hQ : 0 < Q gamma (theta / 4)) (hq : 0 < q gamma (theta / 4))
    (hn : 0 < partJSpectrumCount Q q (theta / 2) gamma)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (h : MultiplyLinearWith (partJGraphBound Q q theta gamma) (partJExponent Q q theta gamma) Gamma) :
    MultiplyLinear gamma ((multipleS theta gamma 2)^9) Gamma := by
  let s := (multipleS theta gamma 2)^9
  have hU16 := partJ_U_ge_sixteen ht ht1 hg hg1
  have hs : 0 < s := by dsimp [s]; positivity
  have halg : MultiplyLinearWith (partJGraphBound Q q theta gamma)
      (partJAlgebraicExponent Q q theta gamma) Gamma :=
    h.weaken (fun _ _ _ => le_rfl)
      (fun _ hr _ => partJAlgebraicExponent_pos hQ hq hn ht hg hr)
      (fun _ hr hr1 => (partJAlgebraicExponent_le hQ hq hn ht ht1 hg hg1 hr).trans
        (partJPowerExponent_le hQ hq hn ht ht1 hg hg1 hr hr1))
  change MultiplyLinearWith (fun rho => (multipleQ (s⁻¹ * rho) gamma 3)^s)
    (fun rho => (multipleC (s⁻¹ * rho) gamma 3)^s) Gamma
  apply halg.weaken
  · intro rho hr hr1
    have hE := partJAlgebraicExponent_pos hQ hq hn ht hg hr
    have hC := multipleC_pos 3 (mul_pos (inv_pos.mpr hs) hr) hg
    have hCE : 0 < (multipleC (s⁻¹ * rho) gamma 3)^s := Real.rpow_pos_of_pos hC s
    have hw := partJ_source_width hQb hqb hQ hq hn ht ht1 hg hg1 hr hr1
    have hb := partJ_graph_width_budget hQ hq hn ht ht1 hg hg1 hr hr1
    calc
      _ ≤ (partJAlgebraicExponent Q q theta gamma rho)⁻¹ := by
        rw [← one_div]
        exact (le_div_iff₀ hE).mpr hb
      _ ≤ ((multipleC (s⁻¹ * rho) gamma 3)^s)⁻¹ := (inv_le_inv₀ hE hCE).mpr hw
      _ = _ := by rw [multipleQ, Real.inv_rpow hC.le]
  · intro rho hr _
    exact Real.rpow_pos_of_pos (multipleC_pos 3 (mul_pos (inv_pos.mpr hs) hr) hg) s
  · intro rho hr hr1
    exact partJ_source_width hQb hqb hQ hq hn ht ht1 hg hg1 hr hr1

/-- The piece parameter fits inside the source's dimension-three budget. -/
theorem partJ_piece_parameter_budget (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma)
    (hg1 : gamma ≤ 1) :
    1 ≤ (multipleS theta gamma 2)^9 ∧
      (multipleS theta gamma 2)^9 ≤
        section16ThetaTwo (section16ThetaOne (theta / 2) gamma 2) * multipleS theta gamma 3 := by
  have hU16 := partJ_U_ge_sixteen ht ht1 hg hg1
  have hU1 : (1 : Real) ≤ multipleS theta gamma 2 := by linarith only [hU16]
  have hU0 : (0 : Real) ≤ multipleS theta gamma 2 := by linarith only [hU16]
  refine ⟨one_le_pow₀ hU1, ?_⟩
  have hb := partJ_base_ge_two ht ht1 hg hg1
  have hb0 : 0 ≤ 2 / (theta * gamma) := by linarith only [hb]
  have hp : 0 < theta * gamma := mul_pos ht hg
  set a := section16ThetaOne (theta / 2) gamma 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; unfold section16ThetaOne; positivity
  clear_value a
  -- a⁻¹ ≤ U
  have hx : (theta * gamma / 8) = (4 * (2 / (theta * gamma)))⁻¹ := by field_simp; ring
  have h4b : 4 * (2 / (theta * gamma)) ≤ (2 / (theta * gamma)) ^ 3 := by
    nlinarith only [hb, mul_le_mul hb hb (by norm_num) hb0]
  have hainv : a⁻¹ ≤ multipleS theta gamma 2 := by
    rw [ha_def]
    unfold section16ThetaOne
    rw [show theta / 2 * gamma / 4 = theta * gamma / 8 by ring, ← inv_pow, hx, inv_inv]
    calc
      (4 * (2 / (theta * gamma))) ^ (2 ^ 2 ^ (2 + 5)) ≤
          ((2 / (theta * gamma)) ^ 3) ^ (2 ^ 2 ^ (2 + 5)) :=
        pow_le_pow_left₀ (by positivity) h4b _
      _ = (2 / (theta * gamma)) ^ (3 * 2 ^ 2 ^ (2 + 5)) := by rw [← pow_mul]
      _ ≤ _ := partJ_base_pow_le_U ht ht1 hg hg1 (by norm_num)
  -- 2^32 ≤ U
  have h32 : (2 : Real) ^ (32 : Nat) ≤ multipleS theta gamma 2 :=
    (pow_le_pow_left₀ (by norm_num) hb 32).trans (partJ_base_pow_le_U ht ht1 hg hg1 (by norm_num))
  -- mass⁻¹ ≤ U^9
  have hmass : (section16ThetaTwo a)⁻¹ ≤ (multipleS theta gamma 2) ^ 9 := by
    unfold section16ThetaTwo
    rw [mul_inv, Real.rpow_neg (by norm_num), inv_inv, ← inv_pow]
    have h32' : (2 : Real) ^ (32 : Real) ≤ multipleS theta gamma 2 := by
      rw [show (32 : Real) = ((32 : Nat) : Real) by norm_num, Real.rpow_natCast]; exact h32
    calc
      (2 : Real) ^ (32 : Real) * a⁻¹ ^ 8 ≤ multipleS theta gamma 2 * (multipleS theta gamma 2) ^ 8 :=
        mul_le_mul h32' (pow_le_pow_left₀ (by positivity) hainv 8) (by positivity) hU0
      _ = (multipleS theta gamma 2) ^ 9 := by ring
  have hmpos : 0 < section16ThetaTwo a := by unfold section16ThetaTwo; positivity
  have hsucc : (multipleS theta gamma 2) ^ 18 ≤ multipleS theta gamma 3 :=
    multipleS_pow_le_succ 2 18 ht ht1 hg hg1 (by norm_num)
  have hprod : (multipleS theta gamma 2) ^ 9 * (section16ThetaTwo a)⁻¹ ≤ multipleS theta gamma 3 := by
    calc
      (multipleS theta gamma 2) ^ 9 * (section16ThetaTwo a)⁻¹ ≤
          (multipleS theta gamma 2) ^ 9 * (multipleS theta gamma 2) ^ 9 :=
        mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = (multipleS theta gamma 2) ^ 18 := by ring
      _ ≤ _ := hsucc
  calc
    (multipleS theta gamma 2) ^ 9 =
        section16ThetaTwo a * ((multipleS theta gamma 2) ^ 9 * (section16ThetaTwo a)⁻¹) := by
      field_simp
    _ ≤ section16ThetaTwo a * multipleS theta gamma 3 :=
      mul_le_mul_of_nonneg_left hprod hmpos.le

/-- **Part J, conditional Section 16 budgeted piece in dimension three.** -/
theorem section16_budgeted_piece_three_of_stackable (hyp : StackableStructureAt 2 Q q)
    (hQb : PolyBoundedControl Q) (hqb : PolyBoundedControl q) :
    Section16BudgetedPieceAt 3 := by
  intro gamma theta hg hg1 ht ht1
  have ht2 : 0 < theta / 2 := by positivity
  have ht21 : theta / 2 ≤ 1 := by linarith
  have ht4 : 0 < theta / 4 := by positivity
  have ht41 : theta / 4 ≤ 1 := by linarith
  obtain ⟨hQ, hq, -⟩ := hyp gamma (theta / 4) hg hg1 ht4 ht41
  have hn := partJSpectrumCount_pos hyp ht2 ht21 hg hg1
  obtain ⟨hs, hbudget⟩ := partJ_piece_parameter_budget ht ht1 hg hg1
  obtain ⟨N0, hN0⟩ := partJ_relation_piece hyp ht ht1 hg hg1
  have hmass : 0 < section16ThetaTwo (section16ThetaOne (theta / 2) gamma 2) := by
    unfold section16ThetaTwo section16ThetaOne; positivity
  refine ⟨section16ThetaTwo (section16ThetaOne (theta / 2) gamma 2), (multipleS theta gamma 2)^9,
    hmass, hs, hbudget, N0, ?_⟩
  intro N _ _ hN Gamma _ hprod hlarge
  obtain ⟨D, hD, hDmass, hML⟩ := hN0 N hN Gamma hprod hlarge
  exact ⟨D, hD, hDmass, hML.partJ_source_control hQb hqb hQ hq hn ht ht1 hg hg1⟩

/-- **Part J: Theorem 16.2 in dimension three**, conditional on a
polynomially bounded stackable dimension-two structure. -/
theorem theorem_16_2_at_three_of_stackable (hyp : StackableStructureAt 2 Q q)
    (hQb : PolyBoundedControl Q) (hqb : PolyBoundedControl q) : Theorem162At 3 :=
  theorem_16_2_of_budgeted_piece (section16_budgeted_piece_three_of_stackable hyp hQb hqb)

/-- **Part J: Corollary 16.11 in dimension three**, under the same hypotheses. -/
theorem corollary_16_11_at_three_of_stackable (hyp : StackableStructureAt 2 Q q)
    (hQb : PolyBoundedControl Q) (hqb : PolyBoundedControl q) : Corollary1611At 3 :=
  Theorem162At.corollary_16_11 (by norm_num) (theorem_16_2_at_three_of_stackable hyp hQb hqb)

end LeanProofs.GowersSzemeredi
