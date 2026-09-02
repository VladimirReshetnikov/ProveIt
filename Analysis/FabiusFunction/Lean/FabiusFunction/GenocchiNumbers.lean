import FabiusFunction.BernoulliStirling

/-!
# Genocchi numbers

The Genocchi numbers `G_n = 2 (1 - 2^n) B_n` have the exponential generating
function `2t/(e^t + 1)`:

`(∑_n G_n t^n/n!) (e^t + 1) = 2t`,

because `2t/(e^t+1) = 2t/(e^t-1) - 4t/(e^{2t}-1) = 2 B(t) - 2 B(2t)` with
`B(t) = t/(e^t-1)` the Bernoulli generating function.  Consequently
`G_1 = 1`, `G_2 = -1` and `G_{2m+1} = 0` for `m ≥ 1`.

## Main results

* `genocchi`, `genocchi_one`, `genocchi_two`, `genocchi_odd`.
* `egf_genocchi_eq`: `∑ G_n t^n/n! = 2 B(t) - 2 B(2t)`.
* `egf_genocchi_mul_exp_add_one`: the generating function.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

/-- The Genocchi numbers `G_n = 2 (1 - 2^n) B_n`. -/
def genocchi (n : ℕ) : ℚ := 2 * (1 - 2 ^ n) * bernoulli n

/-- `G_1 = 1`. -/
theorem genocchi_one : genocchi 1 = 1 := by
  norm_num [genocchi, bernoulli_one]

/-- `G_2 = -1`. -/
theorem genocchi_two : genocchi 2 = -1 := by
  norm_num [genocchi, bernoulli_two]

/-- `G_{2m+1} = 0` for `m ≥ 1`. -/
theorem genocchi_odd (m : ℕ) (hm : 1 ≤ m) : genocchi (2 * m + 1) = 0 := by
  rw [genocchi, bernoulli_eq_zero_of_odd ⟨m, rfl⟩ (by omega), mul_zero]

section

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- `∑_n G_n t^n/n! = 2 B(t) - 2 B(2t)`. -/
theorem egf_genocchi_eq :
    egf A genocchi =
      2 * bernoulliPowerSeries A - 2 * rescale (2 : A) (bernoulliPowerSeries A) := by
  ext n
  rw [coeff_egf, ← map_ofNat (PowerSeries.C : A →+* A⟦X⟧) 2, map_sub, coeff_C_mul, coeff_C_mul,
    coeff_rescale, bernoulliPowerSeries, coeff_mk, genocchi,
    show (2 * (1 - 2 ^ n) * bernoulli n) / (n.factorial : ℚ)
      = 2 * (bernoulli n / n.factorial) - 2 * (2 ^ n * (bernoulli n / n.factorial)) by ring,
    map_sub, map_mul, map_mul, map_mul, map_pow, map_ofNat]

/-- **The Genocchi generating function:** `(∑_n G_n t^n/n!) (e^t + 1) = 2t`. -/
theorem egf_genocchi_mul_exp_add_one : egf A genocchi * (exp A + 1) = 2 * X := by
  have h1 : bernoulliPowerSeries A * (exp A - 1) = X := bernoulliPowerSeries_mul_exp_sub_one A
  have hc : (PowerSeries.C (2 : A)) = (2 : A⟦X⟧) := map_ofNat _ 2
  have he : rescale (2 : A) (exp A) = exp A ^ 2 := by
    rw [exp_pow_eq_rescale_exp, Nat.cast_ofNat]
  have h2 : rescale (2 : A) (bernoulliPowerSeries A) * (exp A ^ 2 - 1) = 2 * X := by
    have h := congrArg (rescale (2 : A)) h1
    rw [map_mul, map_sub, map_one, rescale_X, he, hc] at h
    exact h
  have h3 : (egf A genocchi * (exp A + 1) - 2 * X) * (exp A - 1) = 0 := by
    rw [egf_genocchi_eq]
    linear_combination (2 * (exp A + 1)) * h1 - 2 * h2
  rw [← X_mul_expSubOneDiv,
    show (egf A genocchi * (exp A + 1) - 2 * X) * (X * expSubOneDiv A)
      = X * ((egf A genocchi * (exp A + 1) - 2 * X) * expSubOneDiv A) by ring] at h3
  have h4 := eq_zero_of_X_mul_eq_zero A h3
  rw [(isUnit_expSubOneDiv A).mul_left_eq_zero] at h4
  exact sub_eq_zero.mp h4

end

end Fabius
