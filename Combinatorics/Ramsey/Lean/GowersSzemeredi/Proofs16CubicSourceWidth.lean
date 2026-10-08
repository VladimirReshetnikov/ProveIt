import GowersSzemeredi.Proofs16CubicWidthLowerBound

/-! The cubic cover meets the manuscript's width exponent at the concrete
piece parameter U^8, including the preliminary density halving. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section16_cubic_source_width {theta gamma rho : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hr : 0 < rho) (hr1 : rho ≤ 1) :
    let s := (multipleS theta gamma 1)^8
    (multipleC (s⁻¹ * rho) gamma 2)^s ≤
      section16CubicTwoAlgebraicExponent
        (section16BaseFamilyBound gamma (theta / 4)) (theta / 2) gamma rho := by
  let U := multipleS theta gamma 1
  let R := section16Lemma9R (theta / 2) gamma 1
  let sigma := rho / 4
  let A : Real := ((2 : Nat)^((2 : Nat)^(2 + 8)) : Nat)
  let t := gamma * sigma / (2 * R)
  have hU16 : 16 ≤ U := multipleS_one_ge_sixteen ht ht1 hg hg1
  have hU : 0 < U := by linarith
  have hR1 : 1 ≤ R := by
    have hh := (section16_face_parameter_lift_reserve 1
      (by positivity : 0 < theta / 2) (by linarith : theta / 2 ≤ 1) hg hg1).1
    dsimp [R]
    norm_num [section16Lemma9R] at hh ⊢
    linarith
  have hR : 0 < R := zero_lt_one.trans_le hR1
  have hs : 0 < sigma := by dsimp [sigma]; positivity
  have hs1 : sigma ≤ 1 := by dsimp [sigma]; linarith
  have hA : 1 ≤ A := by
    change (1 : Real) ≤ ((2 : Nat)^((2 : Nat)^(2 + 8)) : Nat)
    exact_mod_cast (one_le_pow₀ (by decide : (1 : Nat) ≤ 2) (n := 2^(2 + 8)))
  have ht0 : 0 < t := by dsimp [t]; positivity
  have hC : multipleC (sigma / (2 * R)) gamma 2 = t^A := by
    unfold multipleC
    rw [show gamma * (sigma / (2 * R)) = t by dsimp [t]; ring]
    exact (Real.rpow_natCast _ _).symm
  have hpow : ((multipleC (sigma / (2 * R)) gamma 2)^R)^ (5 : Nat) = t^(5 * A * R) := by
    rw [hC, ← Real.rpow_mul ht0.le, ← Real.rpow_natCast,
      ← Real.rpow_mul ht0.le]
    exact congrArg (fun z : Real => t^z)
      ((mul_comm (A * R) 5).trans (mul_assoc 5 A R).symm)
  have hsource : (multipleC ((U^8)⁻¹ * rho) gamma 2)^(U^8) =
      (4 * gamma * sigma / U^8)^(A * U^8) := by
    have hb : gamma * ((U^8)⁻¹ * rho) = 4 * gamma * sigma / U^8 := by
      dsimp [sigma]
      ring
    unfold multipleC
    rw [hb, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  have habs := section16_cubic_power_absorption hU16 hA hR
    (section16_cubic_remainder_scale_le ht ht1 hg hg1) hg hg1 hs hs1
  have hlower := section16_cubic_width_lower_bound ht ht1 hg hg1 hs hs1
  change (multipleC ((U^8)⁻¹ * rho) gamma 2)^(U^8) ≤ _
  rw [hsource]
  apply habs.trans
  change ((multipleC (sigma / (2 * R)) gamma 2)^R)^5 * sigma^10 *
    (2 : Real)^(-(84 * U^2 + 75)) / U^14 ≤ _ at hlower
  rw [hpow] at hlower
  simpa only [show 4 * sigma = rho by dsimp [sigma]; ring] using hlower

end LeanProofs.GowersSzemeredi
