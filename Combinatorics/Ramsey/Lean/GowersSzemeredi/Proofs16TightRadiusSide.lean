import GowersSzemeredi.Proofs16TightRadius

/-! Declarations of `Proofs16TightRadius` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

theorem fejer_tightRadiusExponent_large {theta gamma : Real} (k : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    (2 : Real) ^ (40 * (k + 1) ^ 3 + 1) ≤ tightRadiusExponent (fejerThetaOne theta gamma k / 4) := by
  set E := fejerProductExponent k
  have hp : 0 < theta * gamma := mul_pos ht hg
  have hp1 : theta * gamma ≤ 1 := by nlinarith
  have hb4 : (2 : Real) ≤ 4 / (theta * gamma) := (le_div_iff₀ hp).mpr (by nlinarith)
  rw [fejer_tightRadiusExponent_eq k ht hg]
  -- the exponent comparison
  have hE : 40 * (k + 1) ^ 3 + 1 ≤ 105 + 11 * E := by
    have h1 : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
    have h3 : (k + 1) ^ 3 ≤ (2 ^ k) ^ 3 := Nat.pow_le_pow_left h1 3
    have h4 : (2 ^ k) ^ 3 ≤ 2 ^ (4 * k) := by
      rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h5 : 2 ^ (4 * k + 11) ≤ E := by
      show 2 ^ (4 * k + 11) ≤ 2 ^ (3 * k + 7) * (2 ^ (k + 4) * (k + 6))
      calc 2 ^ (4 * k + 11) = 2 ^ (3 * k + 7) * (2 ^ (k + 4) * 1) := by
            rw [mul_one, ← pow_add]; congr 1; omega
        _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
    have h6 : 2 ^ (4 * k + 11) = 2048 * 2 ^ (4 * k) := by rw [pow_add]; ring
    rw [h6] at h5
    generalize 2 ^ (4 * k) = x at *
    nlinarith
  calc (2 : Real) ^ (40 * (k + 1) ^ 3 + 1) ≤ (2 : Real) ^ (105 + 11 * E) :=
        pow_le_pow_right₀ (by norm_num) hE
    _ = (2 : Real) ^ (105 : Nat) * (2 : Real) ^ (11 * E) := by rw [pow_add]
    _ ≤ (2 : Real) ^ (105 : Nat) * (4 / (theta * gamma)) ^ (11 * E) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hb4 _) (by positivity)

end LeanProofs.GowersSzemeredi
