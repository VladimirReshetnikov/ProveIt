import Surreal.Surcomplex.AcosEndpoint

/-!
# The full strong series at the inverse-cosine endpoint

Rescale the inverse-sine strong sum by the half-defect square root.
The remaining series has constant coefficient one, giving both the exact
finite remainder and the valuation in `trigonometry:prop:acosendpoint`.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- The ordinary coefficient series multiplying the endpoint square-root scale. -/
def acosEndpointSeries : PowerSeries ℝ :=
  PowerSeries.mk (fun n => (Nat.centralBinom n : ℝ) / (8 ^ n * (2 * n + 1)))

@[simp] theorem coeff_acosEndpointSeries (n : ℕ) :
    PowerSeries.coeff n acosEndpointSeries =
      (Nat.centralBinom n : ℝ) / (8 ^ n * (2 * n + 1)) :=
  PowerSeries.coeff_mk _ _

/-- The normalized endpoint family is strongly summable at each actual infinitesimal defect. -/
theorem stronglySummable_acosEndpoint (τ : SignSequence.{u})
    (hi : SignSequence.IsInfinitesimal τ) :
    SignSequence.StronglySummable (fun n : ℕ =>
      SignSequence.ofReal ((Nat.centralBinom n : ℝ) / (8 ^ n * (2 * n + 1))) * τ ^ n) :=
  SignSequence.stronglySummable_coeff_mul_powers τ hi _

private theorem acos_endpoint_term (τ : SignSequence.{u}) (hp : 0 ≤ τ) (n : ℕ) :
    2 * (SignSequence.ofReal ((Nat.centralBinom n : ℝ) / (4 ^ n * (2 * n + 1))) *
        SignSequence.sqrt (τ / 2) ^ (2 * n + 1)) =
      SignSequence.sqrt (2 * τ) *
        (SignSequence.ofReal ((Nat.centralBinom n : ℝ) / (8 ^ n * (2 * n + 1))) * τ ^ n) := by
  rw [sqrt_two_mul_eq_two_mul_sqrt_half τ hp, pow_succ, pow_mul,
    SignSequence.sqrt_sq (show 0 ≤ τ / 2 by positivity), div_pow]
  simp only [map_div₀, map_mul, map_pow, map_add, map_natCast, map_ofNat, map_one]
  have he : (8 : SignSequence.{u}) ^ n = 4 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
  rw [he]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The literal strong series in the inverse-cosine endpoint formula. -/
theorem arccosFunction_one_sub_eq_strongSum (τ : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) :
    arccosFunction (1 - τ) = SignSequence.sqrt (2 * τ) *
      SignSequence.strongSum (fun n : ℕ =>
        SignSequence.ofReal ((Nat.centralBinom n : ℝ) / (8 ^ n * (2 * n + 1))) * τ ^ n)
        (stronglySummable_acosEndpoint τ hi) := by
  have hh : SignSequence.IsInfinitesimal (τ / 2) := by
    apply SignSequence.infinitesimal_of_abs_le (y := τ) _ hi
    rw [abs_of_pos hp, abs_of_pos (div_pos hp (by norm_num))]
    linarith
  have hs := SignSequence.infinitesimal_sqrt (show 0 ≤ τ / 2 by positivity) hh
  have hsum := SignSequence.strongSum_const_mul
    (stronglySummable_arcsinTaylor (SignSequence.sqrt (τ / 2)) hs) 2
  have he : (fun n : ℕ =>
      2 * (SignSequence.ofReal ((Nat.centralBinom n : ℝ) / (4 ^ n * (2 * n + 1))) *
        SignSequence.sqrt (τ / 2) ^ (2 * n + 1))) =
      (fun n : ℕ => SignSequence.sqrt (2 * τ) *
        (SignSequence.ofReal ((Nat.centralBinom n : ℝ) / (8 ^ n * (2 * n + 1))) * τ ^ n)) :=
    funext (acos_endpoint_term τ hp.le)
  simp only [he] at hsum
  rw [arccosFunction_one_sub_eq_two_arcsin τ hp hi, arcsinFunction_eq_strongSum _ hs]
  exact hsum.symm.trans (SignSequence.strongSum_const_mul (stronglySummable_acosEndpoint τ hi) _)

/-- The normalized endpoint factor is evaluation of its explicit formal power series. -/
theorem arccosFunction_one_sub_eq_powerSeries (τ : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) :
    arccosFunction (1 - τ) = SignSequence.sqrt (2 * τ) *
      SignSequence.powerSeriesEvaluation τ hi acosEndpointSeries := by
  rw [arccosFunction_one_sub_eq_strongSum τ hp hi, SignSequence.powerSeriesEvaluation_eq_strongSum]
  simp only [coeff_acosEndpointSeries]

/-- The displayed cubic normalized expansion has an exact finite fourth-order remainder. -/
theorem arccosFunction_endpoint_expansion (τ : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) :
    ∃ R : SignSequence.{u}, SignSequence.IsFinite R ∧ SignSequence.standardPart R = 35 / 18432 ∧
      arccosFunction (1 - τ) = SignSequence.sqrt (2 * τ) *
        (1 + τ / 12 + 3 * τ ^ 2 / 160 + 5 * τ ^ 3 / 896 + τ ^ 4 * R) := by
  obtain ⟨R, hR, hr, he⟩ := SignSequence.exists_finite_powerSeries_remainder τ hi acosEndpointSeries 4
  norm_num [coeff_acosEndpointSeries, Finset.sum_range_succ,
    Nat.centralBinom, Nat.choose_succ_succ, map_div₀, map_ofNat] at hr he
  refine ⟨R, hR, hr, ?_⟩
  rw [arccosFunction_one_sub_eq_powerSeries τ hp hi, he]
  ring

/-- The factor remaining after removal of the square-root scale has standard part one. -/
theorem arccosFunction_endpoint_leading_factor (τ : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) :
    ∃ R : SignSequence.{u}, SignSequence.IsFinite R ∧ SignSequence.standardPart R = 1 ∧
      arccosFunction (1 - τ) = SignSequence.sqrt (2 * τ) * R := by
  refine ⟨SignSequence.powerSeriesEvaluation τ hi acosEndpointSeries,
    SignSequence.isFinite_powerSeriesEvaluation τ hi _, ?_,
    arccosFunction_one_sub_eq_powerSeries τ hp hi⟩
  simp [acosEndpointSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]

/-- The finite valuation exponent of the endpoint angle is exactly half that of the defect. -/
theorem valuation_arccosFunction_one_sub (τ : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) :
    SignSequence.valuation (arccosFunction (1 - τ)) =
      ((-SignSequence.leadingExponent τ / 2 : SignSequence.{u}) : WithTop SignSequence.{u}) := by
  obtain ⟨R, hR, hr, he⟩ := arccosFunction_endpoint_leading_factor τ hp hi
  have hv := (SignSequence.valuation_eq_zero_iff_standardPart_ne_zero hR).mpr
    (by rw [hr]; norm_num)
  rw [he, SignSequence.valuation_mul, hv, add_zero,
    SignSequence.valuation_sqrt (show 0 < 2 * τ by positivity),
    SignSequence.leadingExponent_mul (by norm_num : (2 : SignSequence.{u}) ≠ 0) hp.ne']
  have htwo : SignSequence.leadingExponent (2 : SignSequence.{u}) = 0 := by
    simpa only [map_ofNat] using SignSequence.leadingExponent_ofReal (2 : ℝ)
  rw [htwo, zero_add]

/-- The same valuation statement in intrinsic additive-valuation notation. -/
theorem two_nsmul_valuation_arccosFunction_one_sub (τ : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) :
    2 • SignSequence.valuation (arccosFunction (1 - τ)) = SignSequence.valuation τ := by
  rw [valuation_arccosFunction_one_sub τ hp hi, SignSequence.valuation_of_ne_zero hp.ne',
    ← WithTop.coe_nsmul]
  congr 1
  simp only [nsmul_eq_mul]
  ring

end
end Surreal.Surcomplex
