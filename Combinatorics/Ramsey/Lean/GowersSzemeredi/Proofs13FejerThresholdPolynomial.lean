import GowersSzemeredi.Proofs13FejerFrequencyGraph

/-! Polynomial upper bounds for the explicit Fejer modulus threshold.
The ceiling operations are retained in the construction and bounded here. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Absorb a natural ceiling into one additional power of a base at least two. -/
theorem nat_ceil_le_pow_succ {x y : Real} {n : Nat}
    (hx : 2 ≤ x) (hy : 0 ≤ y) (h : y ≤ x ^ n) :
    (Nat.ceil y : Real) ≤ x ^ (n + 1) := by
  have hxone : 1 ≤ x := by linarith only [hx]
  have hp : 1 ≤ x ^ n := one_le_pow₀ hxone
  calc
    _ ≤ y + 1 := (Nat.ceil_lt_add_one hy).le
    _ ≤ x ^ n + x ^ n := add_le_add h hp
    _ = 2 * x ^ n := by ring
    _ ≤ x * x ^ n := mul_le_mul_of_nonneg_right hx (by positivity)
    _ = x ^ (n + 1) := by rw [pow_succ]; ring

/-- Reciprocal power bounds on the three purification parameters give one
power bound for the entire rounded threshold, with explicit exponent. -/
theorem fejerPurificationThreshold_le_power
    {delta rho eta x : Real} {d r e : Nat}
    (hδ : 0 < delta) (hρ : 0 < rho) (hη : 0 < eta) (hx : 2 ≤ x)
    (hd : delta⁻¹ ≤ x ^ d) (hr : rho⁻¹ ≤ x ^ r) (he : eta⁻¹ ≤ x ^ e) :
    (fejerPurificationThreshold delta rho eta : Real) ≤
      x ^ (64 * (r + e + 35) + 15 * d + 132) := by
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hx1 : 1 ≤ x := by linarith only [hx]
  let M := Nat.ceil ((2 : Real) ^ 34 / (rho * eta))
  have hratio : (2 : Real) ^ 34 / (rho * eta) ≤ x ^ 34 * x ^ r * x ^ e := by
    rw [div_eq_mul_inv, mul_inv, ← mul_assoc]
    gcongr
  have hM : (M : Real) ≤ x ^ (r + e + 35) :=
    nat_ceil_le_pow_succ hx (by positivity) (hratio.trans_eq (by ring))
  have hlarge : (2 : Real) ^ 131 * (M : Real) ^ 63 / (rho * eta * delta ^ 15) ≤
      x ^ 131 * (x ^ (r + e + 35)) ^ 63 * (x ^ r * x ^ e * (x ^ d) ^ 15) := by
    rw [div_eq_mul_inv, mul_inv, mul_inv, ← inv_pow]
    gcongr
  have hceil := nat_ceil_le_pow_succ hx (by positivity) (hlarge.trans_eq (by ring) :
    _ ≤ x ^ (63 * (r + e + 35) + r + e + 15 * d + 131))
  unfold fejerPurificationThreshold
  push_cast
  exact max_le ((mul_le_mul hx hM (by positivity) hx0).trans
    ((pow_succ' x _).symm.trans_le (pow_le_pow_right₀ hx1 (by omega))))
    (hceil.trans (pow_le_pow_right₀ hx1 (by omega)))

/-- The explicit frequency-graph threshold is polynomial in 2/alpha.
Its exponent is much smaller than any later double-exponential budget. -/
theorem section13FrequencyGraphThreshold_le_power {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    (section13FrequencyGraphThreshold alpha : Real) ≤ (2 / alpha) ^ ((2 : Nat) ^ 37) := by
  let a := alpha / 2
  let x := 2 / alpha
  have hx : 2 ≤ x := (le_div_iff₀ hα).mpr (by linarith only [hαone])
  have hainv : a⁻¹ = x := by dsimp [a, x]; field_simp
  have hd : (a ^ (14409429 : Nat))⁻¹ ≤ x ^ (14409429 : Nat) := by rw [← inv_pow, hainv]
  have hr : ((a ^ (14409429 : Nat)) ^ 97 * a ^ 336)⁻¹ ≤
      x ^ (14409429 * 97 + 336 : Nat) := by
    rw [mul_inv_rev, ← inv_pow, ← inv_pow, ← inv_pow, hainv, ← pow_mul, pow_add]
    exact le_of_eq (mul_comm _ _)
  have he : (((1 / 2 : Real) ^ (44 : Nat))⁻¹) ≤ x ^ (44 : Nat) := by
    rw [← inv_pow]
    simpa only [one_div, inv_inv] using pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 2) hx 44
  have h := fejerPurificationThreshold_le_power (by positivity : 0 < a ^ (14409429 : Nat))
    (by positivity : 0 < (a ^ (14409429 : Nat)) ^ 97 * a ^ 336)
    (by norm_num : 0 < (1 / 2 : Real) ^ (44 : Nat)) hx hd hr he
  exact h.trans (pow_le_pow_right₀ (by linarith only [hx]) (by norm_num))

end LeanProofs.GowersSzemeredi
