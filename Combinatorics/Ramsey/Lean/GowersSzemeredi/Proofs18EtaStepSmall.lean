import GowersSzemeredi.Proofs18GenericEnvelopeBase

/-! **The η and `yIn` steps with a polynomial side condition** (Notes L.16j).

`GenParams.eta_step` and `GenParams.yIn_step` ask for `fixDeg k ≤ m`, with
`fixDeg k = 2^(k+5) + 7`. They use it only to absorb
`2^(2(k+2)³)·2^(k+1)·(2/α)²` and `2·(2(k+3))^(k+3)` into `(2/α)^(2^m)`, and
`m ≥ 3(k+4)²` already suffices (`cube_le_two_pow_sq`). At the class constant
`4` the density degree is about `28·2^k < 32·2^k`, so the printed side
condition would raise one step from `28·2^k` to `32·2^k`. The envelope would
then tend to `64·2^k` and lose `d + 4`. The bounds below instantiate the
shared scalar-absorption estimates using this polynomial budget. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The constants of the η and `yIn` steps fit `2^(3(k+4)²)`. -/
theorem cube_le_two_pow_sq (k : Nat) : 2 * (k + 2) ^ 3 + k + 3 ≤ 2 ^ (3 * (k + 4) ^ 2) ∧
    2 * (2 * (k + 3)) ^ (k + 3) ≤ 2 ^ (3 * (k + 4) ^ 2) := by
  constructor
  · have h1 : (k + 2) ^ 3 ≤ (2 ^ (k + 2)) ^ 3 := Nat.pow_le_pow_left Nat.lt_two_pow_self.le 3
    have h2 : (2 ^ (k + 2)) ^ 3 = 2 ^ (3 * k + 6) := by rw [← pow_mul]; ring_nf
    have h3 : k + 3 ≤ 2 ^ (3 * k + 6) :=
      (Nat.lt_two_pow_self (n := k + 3)).le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h4 : 2 ^ (3 * k + 8) = 4 * 2 ^ (3 * k + 6) := by
      rw [show 3 * k + 8 = (3 * k + 6) + 2 by ring, pow_add]; ring
    have h5 : 2 ^ (3 * k + 8) ≤ 2 ^ (3 * (k + 4) ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    omega
  · have hk3 : 2 * (k + 3) ≤ 2 ^ (k + 3) := by
      have := Nat.lt_two_pow_self (n := k + 2); rw [pow_succ]; omega
    calc 2 * (2 * (k + 3)) ^ (k + 3) ≤ 2 * (2 ^ (k + 3)) ^ (k + 3) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hk3 _)
      _ = 2 ^ ((k + 3) * (k + 3) + 1) := by rw [← pow_mul, pow_succ]; ring
      _ ≤ 2 ^ (3 * (k + 4) ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

namespace GenParams

/-- `η` from the single-piece density. -/
theorem eta_step_small {alpha d : Real} {k m : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (hd0 : 0 < d) (hd1 : d ≤ 1) (hdi : d⁻¹ ≤ (2 / alpha) ^ (2 ^ m)) (hm : 3 * (k + 4) ^ 2 ≤ m) :
    0 < (2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)) * (d / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4) ∧
      (2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)) * (d / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4) ≤
        alpha / 8 ∧
      ((2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)) * (d / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4))⁻¹ ≤
        (2 / alpha) ^ (2 ^ (m + 1)) := by
  exact eta_step_of_cube_le ha ha2 hd0 hd1 hdi
    ((cube_le_two_pow_sq k).1.trans (Nat.pow_le_pow_right (by norm_num) hm))

/-- `yIn` from `η`. -/
theorem yIn_step_small {alpha e : Real} {k m : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (he0 : 0 < e) (he8 : e ≤ alpha / 8) (hei : e⁻¹ ≤ (2 / alpha) ^ (2 ^ m)) (hm : 3 * (k + 4) ^ 2 ≤ m) :
    0 < (e / 2) / (2 * (k + 1 + 2 : Nat) : Real) ^ (k + 1 + 2) ∧
      (e / 2) / (2 * (k + 1 + 2 : Nat) : Real) ^ (k + 1 + 2) ≤ alpha ∧
      ((e / 2) / (2 * (k + 1 + 2 : Nat) : Real) ^ (k + 1 + 2))⁻¹ ≤ (2 / alpha) ^ (2 ^ (m + 1)) := by
  exact yIn_step_of_den_le ha ha2 he0 he8 hei
    ((cube_le_two_pow_sq k).2.trans (Nat.pow_le_pow_right (by norm_num)
      (hm.trans (Nat.le_of_lt (Nat.lt_two_pow_self (n := m))))))

end GenParams

end LeanProofs.GowersSzemeredi
