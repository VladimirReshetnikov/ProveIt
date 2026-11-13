import RadixBitWindow
import PaddedRadixDigits
set_option autoImplicit false
namespace ByteWindow
open PaddedRadixDigits

theorem bit_offset (L : List ℕ) (hL : ∀ x ∈ L, x < 2^67) (k : ℕ) :
    (Nat.ofDigits (2^67) L / 2^k) % 256 =
      (digit L (k/67) / 2^(k%67) + digit L (k/67+1) * 2^(67-k%67)) % 256 := by
  have hk : 2^k = (2^67)^(k/67) * 2^(k%67) := by
    calc
      2^k = 2^(67*(k/67)+k%67) := by rw [Nat.div_add_mod]
      _ = (2^67)^(k/67) * 2^(k%67) := by rw [pow_add, pow_mul]
  have hs : k%67 < 67 := Nat.mod_lt _ (by decide)
  have hb : 0 < 2^67 := by norm_num
  have h0 := ofDigits_digit (2^67) L hb hL (k/67)
  have h1 := ofDigits_digit (2^67) L hb hL (k/67+1)
  rw [hk, ← Nat.div_div_eq_div_mul, RadixBitWindow.window _ _ hs, h0]
  rw [Nat.div_div_eq_div_mul, ← pow_succ, h1]

theorem byte (L : List ℕ) (hL : ∀ x ∈ L, x < 2^67) (j : ℕ) :
    (Nat.ofDigits (2^67) L / 2^(8*j)) % 256 =
      (digit L ((8*j)/67) / 2^((8*j)%67) +
        digit L ((8*j)/67+1) * 2^(67-(8*j)%67)) % 256 :=
  bit_offset L hL (8*j)

#print axioms ByteWindow.bit_offset
#print axioms ByteWindow.byte
end ByteWindow
