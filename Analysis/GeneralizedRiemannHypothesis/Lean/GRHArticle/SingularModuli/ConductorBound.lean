import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Tactic.Linarith

/-!
# The conductor cutoff for the small class-number census

The prime two accounts for the only loss in the bound for the square of
Euler's totient. The order class-number estimate then gives `f ≤ 18h²`.
-/

namespace GRHArticle.SingularModuli

private theorem le_evenFactor_mul_totient_sq (n : ℕ) :
    n ≤ (if 2 ∣ n then 2 else 1) * n.totient ^ 2 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one => decide
  | prime_pow p k hp hk =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    rw [Nat.totient_prime_pow_succ hp, pow_succ p]
    have hpk : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.pos
    by_cases hp2 : p = 2
    · subst p
      rw [if_pos (dvd_mul_left _ _)]
      simp
      nlinarith only [Nat.mul_le_mul_left (2 ^ k) hpk]
    · have h2p : ¬2 ∣ p := fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 hd).symm
      have hnp : ¬2 ∣ p ^ k * p := by
        rw [← pow_succ]
        exact fun h => h2p (Nat.prime_two.dvd_of_dvd_pow h)
      rw [if_neg hnp, one_mul, mul_pow]
      have hthree : 3 ≤ p := by have := hp.two_le; omega
      have hpbound : p ≤ (p - 1) ^ 2 := by
        have h : p = p - 1 + 1 := by omega
        nlinarith [show 2 ≤ p - 1 by omega, Nat.sub_mul (p - 1) 2 (p - 1)]
      have hs : p ^ k ≤ (p ^ k) ^ 2 := by
        simpa [sq] using Nat.mul_le_mul_left (p ^ k) hpk
      exact Nat.mul_le_mul hs hpbound
  | coprime a b _ _ hab ha hb =>
    simp only [Nat.totient_mul hab, mul_pow, Nat.prime_two.dvd_mul]
    have hprod := Nat.mul_le_mul ha hb
    by_cases h₂a : 2 ∣ a <;> by_cases h₂b : 2 ∣ b
    · exact False.elim (Nat.prime_two.not_dvd_one (hab ▸ Nat.dvd_gcd h₂a h₂b))
    all_goals simpa [h₂a, h₂b, mul_left_comm, mul_comm, mul_assoc] using hprod

/-- Euler's totient satisfies `n ≤ 2 φ(n)²` for every natural number. -/
theorem le_two_mul_totient_sq (n : ℕ) : n ≤ 2 * n.totient ^ 2 :=
  (le_evenFactor_mul_totient_sq n).trans (Nat.mul_le_mul_right _ (by split <;> decide))

/-- The unit-index estimate `φ(f) ≤ 3h` gives the conductor bound used in
the finite discriminant search of `smd:sec:small`. -/
theorem conductor_le_of_totient_bound {f h : ℕ} (hf : f.totient ≤ 3 * h) :
    f ≤ 18 * h ^ 2 := by
  calc
    f ≤ 2 * f.totient ^ 2 := le_two_mul_totient_sq f
    _ ≤ 2 * (3 * h) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hf 2)
    _ = _ := by ring

end GRHArticle.SingularModuli
