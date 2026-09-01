import FabiusFunction.JacobiTripleProduct

/-!
# Quasi-periodicity and zeros of the bilateral theta series

The bilateral theta series `θ(z;q) = ∑_{k∈ℤ} q^{k(k-1)/2} z^k` (`‖q‖ < 1`,
`z ≠ 0`) is, by Jacobi's triple product, the product
`(-z;q)_∞ (-q/z;q)_∞ (q;q)_∞`.

* **Quasi-periodicity** `θ(qz;q) = z⁻¹ θ(z;q)` is a reindexing of the series:
  `q^{k(k-1)/2} (qz)^k = q^{(k+1)k/2} z^k`, and shifting `k ↦ k+1` produces
  the factor `z⁻¹`.
* **The zeros** are exactly the points `z = -q^m`, `m ∈ ℤ`: the product
  vanishes iff a factor `1 + zq^j` or `1 + q^{j+1}/z` vanishes.

## Main declarations

* `bilateralTheta`, `hasSum_bilateralTheta`, `bilateralTheta_eq_prod`.
* `thetaExponent_add_one`, `pow_thetaExponent_add_one`.
* `bilateralTheta_mul_left`: `θ(qz;q) = z⁻¹ θ(z;q)`.
* `bilateralTheta_eq_zero_iff`: the zero set.
-/

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace Fabius

/-- `θ(k+1) = θ(k) + k` for the integer exponent `θ(k) = k(k-1)/2`. -/
theorem thetaExponent_add_one (k : ℤ) : (thetaExponent (k + 1) : ℤ) = thetaExponent k + k := by
  have h1 := two_mul_thetaExponent (k + 1)
  have h2 := two_mul_thetaExponent k
  have h3 : (2 : ℤ) * (thetaExponent (k + 1) : ℤ) = 2 * (thetaExponent k : ℤ) + 2 * k := by
    rw [h1, h2]
    ring
  omega

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- `q^{θ(k+1)} = q^{θ(k)} q^k` for `q ≠ 0`. -/
theorem pow_thetaExponent_add_one {q : 𝕜} (hq0 : q ≠ 0) (k : ℤ) :
    (q ^ thetaExponent (k + 1) : 𝕜) = q ^ thetaExponent k * q ^ k := by
  rw [← zpow_natCast, ← zpow_natCast, thetaExponent_add_one, zpow_add₀ hq0]

/-- The bilateral theta series `θ(z;q) = ∑_{k∈ℤ} q^{k(k-1)/2} z^k`. -/
noncomputable def bilateralTheta (q z : 𝕜) : 𝕜 := ∑' k : ℤ, q ^ thetaExponent k * z ^ k

/-- The bilateral theta summands sum to `bilateralTheta` when `‖q‖ < 1` and `z ≠ 0`. -/
theorem hasSum_bilateralTheta {q : 𝕜} (hq : ‖q‖ < 1) {z : 𝕜} (hz : z ≠ 0) :
    HasSum (fun k : ℤ => q ^ thetaExponent k * z ^ k) (bilateralTheta q z) :=
  (hasSum_jacobi_triple_product' hq hz).summable.hasSum

/-- **Jacobi's triple product** for `θ`: `θ(z;q) = (-z;q)_∞ (-q/z;q)_∞ (q;q)_∞`. -/
theorem bilateralTheta_eq_prod {q : 𝕜} (hq : ‖q‖ < 1) {z : 𝕜} (hz : z ≠ 0) :
    bilateralTheta q z =
      qPochhammerInfIn (-z) q * qPochhammerInfIn (-(q / z)) q * qPochhammerInfIn q q :=
  (hasSum_jacobi_triple_product' hq hz).tsum_eq

/-- **Quasi-periodicity**: `θ(qz;q) = z⁻¹ θ(z;q)`. -/
theorem bilateralTheta_mul_left {q : 𝕜} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) {z : 𝕜} (hz : z ≠ 0) :
    bilateralTheta q (q * z) = z⁻¹ * bilateralTheta q z := by
  have h := ((hasSum_bilateralTheta hq hz).mul_left z⁻¹)
  have h' := (Equiv.addRight (1 : ℤ)).hasSum_iff.mpr h
  show ∑' k : ℤ, q ^ thetaExponent k * (q * z) ^ k = z⁻¹ * bilateralTheta q z
  refine (h'.congr_fun fun k => ?_).tsum_eq
  simp only [Function.comp_apply, Equiv.coe_addRight]
  rw [pow_thetaExponent_add_one hq0, mul_zpow, zpow_add_one₀ hz, inv_mul_eq_div, eq_div_iff hz]
  ring

/-- **The zeros of the theta function**: for `‖q‖ < 1`, `q ≠ 0`, `z ≠ 0`,
`θ(z;q) = 0` if and only if `z = -q^m` for some integer `m`. -/
theorem bilateralTheta_eq_zero_iff {q : 𝕜} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) {z : 𝕜} (hz : z ≠ 0) :
    bilateralTheta q z = 0 ↔ ∃ m : ℤ, z = -q ^ m := by
  have hI : ¬ qPochhammerInfIn q q = 0 := qPochhammerInfIn_self_ne_zero hq
  rw [bilateralTheta_eq_prod hq hz, mul_eq_zero, mul_eq_zero, qPochhammerInfIn_eq_zero_iff _ hq,
    qPochhammerInfIn_eq_zero_iff _ hq]
  simp only [hI, or_false]
  constructor
  · rintro (⟨j, hj⟩ | ⟨j, hj⟩)
    · refine ⟨-(j : ℤ), ?_⟩
      have hqj : q ^ j ≠ 0 := pow_ne_zero j hq0
      have h2 : z * q ^ j = -1 := by linear_combination -hj
      rw [zpow_neg, zpow_natCast]
      calc z = z * q ^ j * (q ^ j)⁻¹ := by rw [mul_inv_cancel_right₀ hqj]
        _ = -(q ^ j)⁻¹ := by rw [h2, neg_one_mul]
    · refine ⟨(j : ℤ) + 1, ?_⟩
      have h2 : q * z⁻¹ * q ^ j = -1 := by linear_combination -hj
      rw [zpow_add_one₀ hq0, zpow_natCast]
      calc z = -(z * (q * z⁻¹ * q ^ j)) := by rw [h2, mul_neg_one, neg_neg]
        _ = -(q ^ j * q) := by
          rw [show z * (q * z⁻¹ * q ^ j) = q * q ^ j * (z * z⁻¹) by ring, mul_inv_cancel₀ hz,
            mul_one, mul_comm q]
  · rintro ⟨m, rfl⟩
    rcases le_or_gt m 0 with hm | hm
    · left
      refine ⟨(-m).toNat, ?_⟩
      rw [neg_neg, ← zpow_natCast, Int.toNat_of_nonneg (by omega), ← zpow_add₀ hq0,
        add_neg_cancel, zpow_zero]
    · right
      refine ⟨(m - 1).toNat, ?_⟩
      rw [div_neg, neg_neg, ← zpow_natCast, Int.toNat_of_nonneg (by omega), div_mul_eq_mul_div,
        mul_comm q, ← zpow_add_one₀ hq0, show m - 1 + 1 = m by omega, div_self (zpow_ne_zero m hq0)]

end Fabius
