import GowersSzemeredi.Proofs16CubicPowerAbsorption
import GowersSzemeredi.Proofs16CubicOuterScaleBudget

/-! An algebraic lower bound for the actual cubic width expression, after
bounding the spectrum, family, and sample counts by the outer scale. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section16_cubic_scalar_width {U u sigma V Q M q r : Real}
    (hU : 0 < U) (hu : 0 < u) (hs : 0 < sigma)
    (hV : 0 < V) (hQ : 0 < Q) (hM : 0 < M) (hq : 0 < q) (hr : 0 ≤ r)
    (hVU : V ≤ U^2) (hQU : Q ≤ U^2) (hqU : q ≤ U)
    (hMs : M ≤ 7 / (sigma * u)) :
    (2 : Real)^(-(75 : Real)) * u^5 * sigma^10 * r / U^14 ≤
      ((u * ((2 : Real)^(-(27 : Real)) * (sigma / 2)^3 / Q^4 * r) / 2) *
        ((2 : Real)^(-(27 : Real)) * sigma^3 / (M * q)^4) / 4) / (10 * V) := by
  have hd : V * Q^4 * M^4 * q^4 ≤
      U^2 * (U^2)^4 * (7 / (sigma * u))^4 * U^4 := by
    exact mul_le_mul (mul_le_mul (mul_le_mul hVU
      (pow_le_pow_left₀ hQ.le hQU 4) (by positivity) (by positivity))
      (pow_le_pow_left₀ hM.le hMs 4) (by positivity) (by positivity))
      (pow_le_pow_left₀ hq.le hqU 4) (by positivity) (by positivity)
  have hfrac := div_le_div_of_nonneg_left
    (show 0 ≤ (2 : Real)^(-(54 : Real)) * u * sigma^6 * r / 640 by positivity)
    (show 0 < V * Q^4 * M^4 * q^4 by positivity) hd
  have hlarge :
      ((2 : Real)^(-(54 : Real)) * u * sigma^6 * r / 640) /
        (U^2 * (U^2)^4 * (7 / (sigma * u))^4 * U^4) =
      ((2 : Real)^(-(54 : Real)) / (640 * 7^4)) * u^5 * sigma^10 * r / U^14 := by
    field_simp
  have hsmall :
      ((2 : Real)^(-(54 : Real)) * u * sigma^6 * r / 640) /
        (V * Q^4 * M^4 * q^4) =
      ((u * ((2 : Real)^(-(27 : Real)) * (sigma / 2)^3 / Q^4 * r) / 2) *
        ((2 : Real)^(-(27 : Real)) * sigma^3 / (M * q)^4) / 4) / (10 * V) := by
    norm_num [Real.rpow_neg, Real.rpow_ofNat]
    ring
  rw [hlarge, hsmall] at hfrac
  apply le_trans ?_ hfrac
  have hc : (2 : Real)^(-(75 : Real)) ≤ (2 : Real)^(-(54 : Real)) / (640 * 7^4) := by
    norm_num [Real.rpow_neg, Real.rpow_ofNat]
  gcongr

/-- The one-dimensional recurrence with three graphs per spectrum member. -/
theorem section16_cubic_recurrence_eq (q : Nat) :
    section16RecurrenceExponent 1 (3 * q) = (2 : Real)^(-(84 * (q : Real))) := by
  unfold section16RecurrenceExponent section16K
  norm_num only [Nat.add_eq, Nat.reducePow, Nat.reduceMul, Nat.cast_ofNat]
  rw [← Real.rpow_intCast]
  push_cast
  rw [show (128 : Real) = 2 ^ (7 : Real) by norm_num,
    ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 2)]
  congr 1
  ring

/-- The inverse graph-count control is exactly the remainder width factor. -/
theorem section16_remainder_power_inv (sigma theta gamma : Real) (k : Nat)
    (hC : 0 ≤ multipleC (sigma / (2 * section16Lemma9R theta gamma k)) gamma (k + 1)) :
    (section16Lemma9QBound sigma theta gamma k)⁻¹ =
      (multipleC (sigma / (2 * section16Lemma9R theta gamma k)) gamma (k + 1)) ^
        section16Lemma9R theta gamma k := by
  simp only [section16Lemma9QBound, multipleQ, Real.inv_rpow hC, inv_inv]

end LeanProofs.GowersSzemeredi
