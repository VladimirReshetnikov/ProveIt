import Mathlib

/-! Power budgets for covers composed at fixed tolerances. The number of
candidates multiplies, but its exponent adds. These arithmetic lemmas make
no assumption about the existence of the covers. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- A family of at most `2^k` factors, each bounded by `X^(2^m)`, costs
only `k` additional bits in the exponent. -/
theorem finite_cover_product_pw {ι : Type*} (E : Finset ι) {X : Real} {m k : Nat}
    (hX : 1 ≤ X) (hcard : E.card ≤ 2 ^ k) (q : ι → Real)
    (hq0 : ∀ i ∈ E, 0 ≤ q i) (hq : ∀ i ∈ E, q i ≤ X ^ (2 ^ m)) :
    ∏ i ∈ E, q i ≤ X ^ (2 ^ (m + k)) := by
  calc ∏ i ∈ E, q i ≤ ∏ _i ∈ E, X ^ (2 ^ m) :=
        Finset.prod_le_prod hq0 hq
    _ = X ^ (2 ^ m * E.card) := by rw [Finset.prod_const, ← pow_mul]
    _ ≤ X ^ (2 ^ m * 2 ^ k) :=
        pow_le_pow_right₀ hX (Nat.mul_le_mul_left _ hcard)
    _ = X ^ (2 ^ (m + k)) := by rw [pow_add]

/-- The exact exponent is the sum of the individual candidate budgets. -/
theorem finite_cover_product_pw_sum {ι : Type*} (E : Finset ι) {X : Real}
    (a : ι → Nat) (q : ι → Real)
    (hq0 : ∀ i ∈ E, 0 ≤ q i) (hq : ∀ i ∈ E, q i ≤ X ^ (a i)) :
    ∏ i ∈ E, q i ≤ X ^ (∑ i ∈ E, a i) := by
  calc ∏ i ∈ E, q i ≤ ∏ i ∈ E, X ^ (a i) := Finset.prod_le_prod hq0 hq
    _ = X ^ (∑ i ∈ E, a i) := by rw [Finset.prod_pow_eq_pow_sum]

/-- A single pigeonhole after a joint cover loses one factor of the input
density; the candidate budget contributes its additive exponent. -/
theorem finite_cover_density_inv_pw {ι : Type*} (E : Finset ι) {X theta : Real}
    {m t k : Nat} (hX : 2 ≤ X) (ht : 0 < theta)
    (hti : theta⁻¹ ≤ X ^ (2 ^ t)) (hcard : E.card ≤ 2 ^ k) (q : ι → Real)
    (hq0 : ∀ i ∈ E, 0 < q i) (hq : ∀ i ∈ E, q i ≤ X ^ (2 ^ m)) :
    (theta / 2 / (∏ i ∈ E, q i))⁻¹ ≤ X ^ (2 ^ (max t (m + k) + 2)) := by
  have hX1 : 1 ≤ X := by linarith
  have hp := finite_cover_product_pw E hX1 hcard q (fun i hi => (hq0 i hi).le) hq
  have hti' : theta⁻¹ ≤ X ^ (2 ^ max t (m + k)) :=
    hti.trans (pow_le_pow_right₀ hX1 (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)))
  have hp' : (∏ i ∈ E, q i) ≤ X ^ (2 ^ max t (m + k)) :=
    hp.trans (pow_le_pow_right₀ hX1 (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)))
  rw [show (theta / 2 / (∏ i ∈ E, q i))⁻¹ =
      (∏ i ∈ E, q i) * (2 * theta⁻¹) by
    simp only [div_eq_mul_inv, mul_inv, inv_inv]; ring]
  calc (∏ i ∈ E, q i) * (2 * theta⁻¹)
      ≤ X ^ (2 ^ max t (m + k)) * (X * X ^ (2 ^ max t (m + k))) :=
        mul_le_mul hp' (mul_le_mul hX hti' (inv_pos.mpr ht).le (by linarith))
          (by positivity) (by positivity)
    _ = X ^ (2 ^ max t (m + k) + (1 + 2 ^ max t (m + k))) := by
        rw [pow_add, pow_add, pow_one]
    _ ≤ X ^ (2 ^ (max t (m + k) + 2)) := by
        apply pow_le_pow_right₀ hX1
        rw [pow_add]
        have : 1 ≤ 2 ^ max t (m + k) := Nat.one_le_two_pow
        norm_num
        omega

end LeanProofs.GowersSzemeredi
