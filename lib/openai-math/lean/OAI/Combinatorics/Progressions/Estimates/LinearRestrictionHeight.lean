import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

def linearRestrictionHeight (n m d H K : ℕ) : ℕ :=
  (((n + 1) ^ d * K) * (m * H + 1) ^ d) *
    (K ^ ((n + 1) ^ d) * H ^ ((n * m) * d))

theorem linearRestrictionHeight_pos (n m d : ℕ) {H K : ℕ}
    (hH : 1 ≤ H) (hK : 1 ≤ K) : 0 < linearRestrictionHeight n m d H K := by
  unfold linearRestrictionHeight
  positivity

theorem linearRestrictionHeight_one_le (n m d : ℕ) {H K : ℕ}
    (hH : 1 ≤ H) (hK : 1 ≤ K) : 1 ≤ linearRestrictionHeight n m d H K :=
  linearRestrictionHeight_pos n m d hH hK

theorem linearRestrictionHeight_mono {n n' m m' d H H' K K' : ℕ}
    (hH : 1 ≤ H) (hK : 1 ≤ K) (hn : n ≤ n') (hm : m ≤ m')
    (hHH' : H ≤ H') (hKK' : K ≤ K') :
    linearRestrictionHeight n m d H K ≤ linearRestrictionHeight n' m' d H' K' := by
  have hN : (n + 1) ^ d ≤ (n' + 1) ^ d :=
    pow_le_pow_left₀ (Nat.zero_le _) (Nat.add_le_add_right hn 1) d
  have hM : (m * H + 1) ^ d ≤ (m' * H' + 1) ^ d :=
    pow_le_pow_left₀ (Nat.zero_le _)
      (Nat.add_le_add_right (Nat.mul_le_mul hm hHH') 1) d
  have hKP : K ^ ((n + 1) ^ d) ≤ K' ^ ((n' + 1) ^ d) :=
    (pow_le_pow_left₀ (Nat.zero_le _) hKK' _).trans
      (pow_le_pow_right₀ (hK.trans hKK') hN)
  have hHP : H ^ ((n * m) * d) ≤ H' ^ ((n' * m') * d) :=
    (pow_le_pow_left₀ (Nat.zero_le _) hHH' _).trans
      (pow_le_pow_right₀ (hH.trans hHH')
        (Nat.mul_le_mul_right d (Nat.mul_le_mul hn hm)))
  exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hN hKK') hM)
    (Nat.mul_le_mul hKP hHP)

end Erdos3

end

end OAI
