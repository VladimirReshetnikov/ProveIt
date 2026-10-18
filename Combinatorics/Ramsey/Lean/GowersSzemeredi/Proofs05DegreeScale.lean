import GowersSzemeredi.Proofs05DegreeStep

/-!
# Real-power and rounding budgets for the polynomial degree step

This separates the analytic rounding calculation from the large integer
threshold comparison. With x = r^(1/D), the coarse target is floor(x^(2K)).
Both possible child lengths are controlled, including target minus one.
-/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- The real-variable calculation behind the degree step. D is the new
partition constant and K the previous one. -/
theorem polynomial_degree_scale_real (K D d T r v : Nat) (x gamma : Real)
    (hK : 1 ≤ K) (hD : 8 * K ≤ D) (hx : 4 ≤ x)
    (hr : (r : Real) = x ^ D) (hv : (v : Real) ≤ x)
    (hthreshold : 2 * ((T : Real) + 1) ≤ x ^ (2 * K))
    (hgamma : ((2 * K * d + 4 : Nat) : Real) ≤ (D : Real) * gamma) :
    ∃ u : Nat, 1 ≤ u ∧ u ^ 4 ≤ r ∧
      ∀ L : Nat, L = u - 1 ∨ L = u →
        T < L ∧ (v : Real) ≤ (L : Real) ^ (K : Real)⁻¹ ∧
        (u : Real) ^ d * (r : Real) ^ (-gamma) +
          (L : Real) ^ (-(2 * (K : Real)⁻¹)) ≤
          (r : Real) ^ (-(2 * (D : Real)⁻¹)) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hxy : x ≤ x ^ (2 * K) := le_self_pow₀ hx1 (by omega)
  have hr0 : (0 : Real) < r := by rw [hr]; positivity
  let u := ⌊x ^ (2 * K)⌋₊
  have hu0 : (u : Real) ≤ x ^ (2 * K) := Nat.floor_le (by positivity)
  have hu1 : x ^ (2 * K) < u + 1 := Nat.lt_floor_add_one _
  have herror : (u : Real) ^ d * (r : Real) ^ (-gamma) ≤ 1 / x ^ 4 := by
    rw [Real.rpow_neg hr0.le, ← div_eq_mul_inv,
      div_le_div_iff₀ (Real.rpow_pos_of_pos hr0 gamma) (by positivity)]
    calc (u : Real) ^ d * x ^ 4 ≤ (x ^ (2 * K)) ^ d * x ^ 4 := by gcongr
      _ = x ^ ((2 * K * d + 4 : Nat) : Real) := by rw [Real.rpow_natCast]; ring
      _ ≤ x ^ ((D : Real) * gamma) := Real.rpow_le_rpow_of_exponent_le hx1 hgamma
      _ = 1 * (r : Real) ^ gamma := by rw [one_mul, hr, Real.rpow_natCast_mul hx0.le]
  refine ⟨u, (Nat.one_le_floor_iff _).mpr (by linarith), ?_, fun L hL => ?_⟩
  · have : (u : Real) ^ 4 ≤ r := (pow_le_pow_left₀ (by positivity) hu0 4).trans
      (by rw [← pow_mul, hr]; exact pow_le_pow_right₀ hx1 (by omega))
    exact_mod_cast this
  have hL : x ^ (2 * K) / 2 ≤ L := by
    have : (u : Real) ≤ L + 1 := by exact_mod_cast (by omega : u ≤ L + 1)
    linarith
  have hroot : x ^ 2 / 2 ≤ (L : Real) ^ (K : Real)⁻¹ := by
    rw [← Real.pow_rpow_inv_natCast (by positivity : 0 ≤ x ^ 2 / 2) (by omega : K ≠ 0)]
    gcongr
    calc (x ^ 2 / 2) ^ K = x ^ (2 * K) / 2 ^ K := by rw [div_pow, pow_mul]
      _ ≤ x ^ (2 * K) / 2 := by gcongr; exact le_self_pow₀ one_le_two (by omega)
      _ ≤ L := hL
  have hdiam : (L : Real) ^ (-(2 * (K : Real)⁻¹)) ≤ 4 / x ^ 4 := by
    rw [Real.rpow_neg (Nat.cast_nonneg L), mul_comm, Real.rpow_mul (Nat.cast_nonneg L),
      Real.rpow_two, show (4 : Real) / x ^ 4 = ((x ^ 2 / 2) ^ 2)⁻¹ by ring]
    gcongr
  have hrD : (r : Real) ^ (-(2 * (D : Real)⁻¹)) = 1 / x ^ 2 := by
    rw [Real.rpow_neg hr0.le, mul_comm, Real.rpow_mul hr0.le, hr,
      Real.pow_rpow_inv_natCast hx0.le (by omega : D ≠ 0), Real.rpow_two, inv_eq_one_div]
  refine ⟨by exact_mod_cast (show (T : Real) < L by linarith),
    hv.trans ((show x ≤ x ^ 2 / 2 by nlinarith [sq_nonneg (x - 2)]).trans hroot), ?_⟩
  rw [hrD]
  calc _ ≤ 1 / x ^ 4 + 4 / x ^ 4 := add_le_add herror hdiam
    _ ≤ 1 / x ^ 2 := by
      rw [← add_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (x ^ 2 - 5)]

end LeanProofs.GowersSzemeredi
