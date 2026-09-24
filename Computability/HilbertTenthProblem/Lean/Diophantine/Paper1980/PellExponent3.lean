import Diophantine.Common.PellInt
import Diophantine.Paper1982.PellPowerQuotient
import Diophantine.Paper1980.PellDoubled

/-!
# The exponent decoding of the base-three Pell kernel

With the main parameter `A = a + 3` and `c = ψ_A(J)`, `d = χ_A(J)`, the kernel
equation `d = U + a c + γ(6a + 8)` is the χ-congruence criterion of Lemma 2.22
(1982) with base `3`, target `U` and index `J`: `6a + 8 = 2·A·3 − 3² − 1` and
`a = A − 3`.  Instead of the cubic size conditions of `pow_of_χ_congruence`
(which would need `3^(3J) < A`, not available at the kernel's small scale
`U ≥ 81`), we use the direct congruence `χ_A(J) = 3^J + (A − 3)ψ_A(J) + γ'(6a+8)`
(`Jones1982.exists_positive_pell_power_quotient_int`): then `U ≡ 3^J (mod 6a + 8)`,
and both values lie below the modulus (`EXPLORATION_BASE_THREE_PELL_KERNEL.md`, §5).
-/

namespace Jones1980

namespace Exp3

open Diophantine Pell

/-- `(a + 3)² − 1 = a² + 6a + 8`. -/
theorem sq_sub_one_eq (a : ℕ) : (a + 3) ^ 2 - 1 = a ^ 2 + 6 * a + 8 := by
  have : (a + 3) ^ 2 = a ^ 2 + 6 * a + 9 := by ring
  omega

/-- The exponent decoding `U = 3^J` from `d = U + a c + γ(6a + 8)`, once `U` and `3^J`
both lie below the modulus `6a + 8`. -/
theorem exp_U {a c d γ J U : ℕ} (hA : 1 < a + 3) (ha : 0 < a) (hc : c = ψ hA J) (hd : d = χ hA J)
    (hJ : 2 ≤ J) (hU : U < 6 * a + 8) (h3 : 3 ^ J < 6 * a + 8)
    (E14 : d = U + a * c + γ * (6 * a + 8)) : U = 3 ^ J := by
  obtain ⟨γ', -, hγ'⟩ := Jones1982.exists_positive_pell_power_quotient_int (A := a + 3) (B := 3)
    (L := J) hA (by norm_num) (by omega) hJ
  have h1 : (d : ℤ) = 3 ^ J + a * c + γ' * (6 * a + 8) := by
    rw [hd, hc, hγ']; push_cast; ring
  have h2 : (U : ℤ) + γ * (6 * a + 8) = 3 ^ J + γ' * (6 * a + 8) := by
    have : (d : ℤ) = U + a * c + γ * (6 * a + 8) := by exact_mod_cast E14
    linarith
  have h3' : (U : ℤ) ≡ 3 ^ J [ZMOD (6 * a + 8)] := by
    rw [Int.modEq_iff_dvd]
    exact ⟨(γ : ℤ) - γ', by linear_combination -h2⟩
  have h4 : U ≡ 3 ^ J [MOD 6 * a + 8] := Int.natCast_modEq_iff.1 (by exact_mod_cast h3')
  exact Nat.ModEq.eq_of_lt_of_lt h4 hU h3

end Exp3

end Jones1980
