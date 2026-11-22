import BertrandFactorCount
import Primorial
import BertrandPrimeFactor

/-! Reconstruct a positive integer from bounded tests for divisibility by
prime powers. The exponent bound and the prime bound can be the same M. -/

namespace Bertrand

private theorem hits_one {p : Nat} (hp : 2 ≤ p) (k : Nat) : hits 1 p k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hpow : p^1 ≤ p^(k+1) := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.pow_one] at hpow
    have hn : ¬ p^(k+1) ∣ 1 := fun h => by have := Nat.eq_one_of_dvd_one h; omega
    simp only [hits, ih, if_neg hn, Nat.add_zero]

private theorem different_primes {p r : Nat} (hp : Prime p) (hr : Prime r) (hne : p ≠ r) :
    ¬ p ∣ r := by
  intro hd
  have := Nat.le_of_dvd (show 0 < r by have := hr.1; omega) hd
  exact hr.2 p hp.1 (by omega) hd

/-- Multiplication by a different prime preserves all prime-power tests. -/
private theorem hits_other {p r : Nat} (hp : Prime p) (hr : Prime r) (hne : p ≠ r)
    (a k : Nat) : hits (r*a) p k = hits a p k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hg := Nat.gcd_pow_left_of_gcd_eq_one (k := k+1)
      (prime_gcd_one hp (different_primes hp hr hne))
    have he : p^(k+1) ∣ r*a ↔ p^(k+1) ∣ a := by
      rw [← Nat.dvd_gcd_mul_iff_dvd_mul, hg, Nat.one_mul]
    simp only [hits, ih, he]

/-- Multiplying by p introduces exactly one power test if the upper exponent
bound is shifted up by one. -/
private theorem hits_shift {r : Nat} (hr : 2 ≤ r) (a k : Nat) :
    hits (r*a) r (k+1) = hits a r k + 1 := by
  induction k with
  | zero => simp [hits, Nat.dvd_mul_right]
  | succ k ih =>
    have he : r^(k+2) ∣ r*a ↔ r^(k+1) ∣ a := by
      rw [Nat.pow_succ, Nat.mul_comm (r^(k+1))]
      exact ⟨Nat.dvd_of_mul_dvd_mul_left (by omega), Nat.mul_dvd_mul_left r⟩
    change hits (r*a) r (k+1) + (if r^(k+2) ∣ r*a then 1 else 0) =
      (hits a r k + (if r^(k+1) ∣ a then 1 else 0)) + 1
    simp only [he, ih]
    omega

private theorem hits_same {r a M : Nat} (hr : 2 ≤ r) (ha : 0 < a) (hm : a ≤ M) :
    hits (r*a) r M = hits a r M + 1 := by
  cases M with
  | zero => omega
  | succ k =>
    have hg := Nat.lt_pow_self (n := k+1) hr
    have hn : ¬ r^(k+1) ∣ a := fun h => by have := Nat.le_of_dvd ha h; omega
    rw [hits_shift hr a k]
    simp only [hits, if_neg hn, Nat.add_zero]

private theorem atoms_one (M : Nat) : prod (atomFactor 1 M) M = 1 := by
  have h (p : Nat) : atomFactor 1 M p = 1 := by
    by_cases hb : primeB p = true
    · simp [atomFactor, hb, hits_one ((primeB_spec p).mp hb).1]
    · simp [atomFactor, hb]
  rw [show atomFactor 1 M = (fun _ => 1) from funext h, prod_one]

/-- A single prime extraction step, with the same fixed bound M on both sides. -/
private theorem atoms_mul {r a M : Nat} (hr : Prime r) (ha : 0 < a) (hA : a ≤ M)
    (hR : r ≤ M) :
    prod (atomFactor (r*a) M) M = r * prod (atomFactor a M) M := by
  have changeFactor (p : Nat) :
      atomFactor (r*a) M p = (if p = r then r else 1) * atomFactor a M p := by
    by_cases hsame : p = r
    · subst p
      simp only [atomFactor, (primeB_spec _).mpr hr, if_true, hits_same hr.1 ha hA,
        Nat.pow_succ, Nat.mul_comm]
    · by_cases hb : primeB p = true
      · have h := hits_other ((primeB_spec _).mp hb) hr hsame a M
        simp [atomFactor, hb, hsame, h]
      · simp [atomFactor, hb, hsame]
  have split : atomFactor (r*a) M = fun p => (if p = r then r else 1) * atomFactor a M p :=
    funext changeFactor
  rw [split, prod_mul, prod_single _ (show 0 < r by have := hr.1; omega) hR]

/-- Simultaneously keep every prime and exponent index bounded by M while
peeling off prime divisors. -/
theorem factor_numeral {m M : Nat} (hm : 1 ≤ m) (hM : m ≤ M) :
    prod (atomFactor m M) M = m := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    by_cases h : m = 1
    · subst m; exact atoms_one M
    · obtain ⟨r, hr, a, hprod⟩ := exists_prime_factor (show 2 ≤ m by omega)
      have ha : 0 < a := Nat.pos_of_mul_pos_left (hprod ▸ hm)
      have hrpos : 0 < r := by have := hr.1; omega
      have hra : r ≤ m := Nat.le_of_dvd hm ⟨a, hprod⟩
      have has : a < m := by
        have lt := Nat.mul_lt_mul_of_pos_right (show 1 < r from hr.1) ha
        simpa only [Nat.one_mul, ← hprod] using lt
      have hprev := ih a has ha (by omega)
      rw [hprod, atoms_mul hr ha (by omega) (by omega), hprev]

end Bertrand
