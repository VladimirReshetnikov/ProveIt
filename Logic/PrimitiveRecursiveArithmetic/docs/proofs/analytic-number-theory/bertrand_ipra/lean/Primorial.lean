import Binomial
import BertrandProducts

/-! The elementary primorial bound from Pascal's rows. -/

namespace Bertrand
open Binomial

theorem prime_gcd_one {p a : Nat} (hp : Prime p) (hn : ¬ p ∣ a) : p.gcd a = 1 := by
  have hg := Nat.gcd_dvd_left p a
  have ha := Nat.gcd_dvd_right p a
  have hpos := Nat.pos_of_dvd_of_pos hg (show 0 < p from Nat.lt_of_lt_of_le (by decide) hp.1)
  have hle := Nat.le_of_dvd (show 0 < p by have := hp.1; omega) hg
  by_cases he : p.gcd a = p
  · exact False.elim (hn (he ▸ ha))
  · by_cases h : 2 ≤ p.gcd a
    · exact False.elim (hp.2 _ h (by omega) hg)
    · omega

theorem prime_cancel {p a b : Nat} (hp : Prime p) (ha : ¬ p ∣ a)
    (h : p ∣ a*b) : p ∣ b := by
  have he := Nat.dvd_gcd_mul_iff_dvd_mul.mpr h
  simpa [prime_gcd_one hp ha] using he

theorem prime_not_dvd_one {p : Nat} (hp : Prime p) : ¬ p ∣ 1 := by
  intro h
  have := Nat.le_of_dvd (by decide : 0 < 1) h
  have := hp.1
  omega

theorem dvd_fac {p k : Nat} (hp : 0 < p) (hk : p ≤ k) : p ∣ fac k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h : p = k+1
    · subst p
      exact Nat.dvd_mul_right _ _
    · exact Nat.dvd_mul_left_of_dvd (ih (by omega)) (k+1)

theorem prime_not_dvd_fac {p k : Nat} (hp : Prime p) (hk : k < p) : ¬ p ∣ fac k := by
  induction k with
  | zero => exact prime_not_dvd_one hp
  | succ k ih =>
    have hn : ¬ p ∣ k+1 := fun h => by have := Nat.le_of_dvd (by omega) h; omega
    exact fun h => ih (by omega) (prime_cancel hp hn h)

theorem prime_dvd_choose {p a b : Nat} (hp : Prime p) (ha : a < p) (hb : b < p)
    (hs : p ≤ a+b) : p ∣ choose (a+b) a := by
  have hd := dvd_fac (show 0 < p by have := hp.1; omega) hs
  rw [← factorial_choose a b, Nat.mul_comm (choose _ _)] at hd
  have hn : ¬ p ∣ fac a * fac b :=
    fun h => prime_not_dvd_fac hp hb (prime_cancel hp (prime_not_dvd_fac hp ha) h)
  exact prime_cancel hp hn hd

/-- Keep just primes strictly above the lower endpoint. -/
def upperFactor (lo p : Nat) : Nat := if lo < p then primeFactor p else 1

theorem upperFactor_cases (lo p : Nat) :
    upperFactor lo p = 1 ∨ (lo < p ∧ Prime p ∧ upperFactor lo p = p) := by
  by_cases h : lo < p
  · by_cases hb : primeB p = true
    · exact Or.inr ⟨h, (primeB_spec _).mp hb, by simp [upperFactor, primeFactor, h, hb]⟩
    · exact Or.inl (by simp [upperFactor, primeFactor, h, hb])
  · exact Or.inl (by simp [upperFactor, h])

theorem prime_not_dvd_upper {p lo k : Nat} (hp : Prime p) (hk : k < p) :
    ¬ p ∣ prod (upperFactor lo) k := by
  induction k with
  | zero => exact prime_not_dvd_one hp
  | succ k ih =>
    have hn : ¬ p ∣ upperFactor lo (k+1) := by
      rcases upperFactor_cases lo (k+1) with h | ⟨_, _, h⟩
      · rw [h]; exact prime_not_dvd_one hp
      · rw [h]; exact fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
    intro hd
    rw [prod, Nat.mul_comm] at hd
    exact ih (by omega) (prime_cancel hp hn hd)

theorem upper_divides_middle (m k : Nat) (hk : k ≤ 2*m+1) :
    prod (upperFactor (m+1)) k ∣ choose (2*m+1) m := by
  induction k with
  | zero => exact Nat.one_dvd _
  | succ k ih =>
    have hprior := ih (by omega)
    rw [prod]
    rcases upperFactor_cases (m+1) (k+1) with h | ⟨hlo, hp, h⟩
    · simpa [h] using hprior
    · rw [h]
      have hpr := prime_dvd_choose (a := m) (b := m+1) hp (by omega) hlo (by omega)
      rw [show m+(m+1) = 2*m+1 by omega] at hpr
      have hg := prime_gcd_one hp (prime_not_dvd_upper (lo := m+1) hp (Nat.lt_succ_self k))
      have hl := Nat.gcd_mul_lcm (prod (upperFactor (m+1)) k) (k+1)
      rw [Nat.gcd_comm, hg, Nat.one_mul] at hl
      rw [← hl]
      exact Nat.lcm_dvd hprior hpr

theorem primorial_split (lo k : Nat) (hk : lo ≤ k) :
    primorial k = primorial lo * prod (upperFactor lo) k := by
  let lower := fun p => if p ≤ lo then primeFactor p else 1
  have h : primeFactor = fun p => lower p * upperFactor lo p := by
    funext p
    by_cases hp : p ≤ lo
    · simp [lower, upperFactor, hp, show ¬ lo < p by omega]
    · simp [lower, upperFactor, hp, show lo < p by omega]
  unfold primorial
  rw [h, prod_mul]
  change prod lower k * prod (upperFactor lo) k = _
  rw [show prod lower k = prod primeFactor lo from prod_cut _ hk, ← h]

theorem primorial_odd (m : Nat) : primorial (2*m+1) ≤ primorial (m+1) * 4^m := by
  rw [primorial_split (m+1) (2*m+1) (by omega)]
  have hpos := choose_pos m (m+1)
  rw [show m+(m+1) = 2*m+1 by omega] at hpos
  exact Nat.mul_le_mul_left _ (Nat.le_trans
    (Nat.le_of_dvd hpos (upper_divides_middle m (2*m+1) (Nat.le_refl _)))
    (odd_middle_upper m))

theorem primorial_bound (n : Nat) : primorial n ≤ 4^n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hsmall : n ≤ 2
    · have h : n=0 ∨ n=1 ∨ n=2 := by omega
      rcases h with rfl | rfl | rfl <;> decide
    let m := n/2
    have hmod := Nat.mod_add_div n 2
    have hm : m+1 < n := by dsimp [m]; omega
    by_cases heven : n%2=0
    · have he : n = 2*m := by dsimp [m]; omega
      have hd : 2 ∣ n := ⟨m, he⟩
      have hn : ¬ Prime n := fun hp => hp.2 2 (by decide) (by omega) hd
      have hb : ¬ primeB n = true := fun h => hn ((primeB_spec _).mp h)
      have hf : primeFactor n = 1 := by simp [primeFactor, hb]
      have hprior := ih (n-1) (by omega)
      have hs : n-1+1 = n := by omega
      have hrec : primorial n = primorial (n-1) := by
        calc
          primorial n = prod primeFactor ((n-1)+1) := congrArg (prod primeFactor) hs.symm
          _ = primorial (n-1) * primeFactor n := by rw [prod, hs]; rfl
          _ = primorial (n-1) := by rw [hf, Nat.mul_one]
      rw [hrec]
      exact Nat.le_trans hprior (Nat.pow_le_pow_right (by decide) (by omega))
    · have ho : n = 2*m+1 := by dsimp [m]; omega
      have hodd := primorial_odd m
      have hpow := Nat.mul_le_mul_right (4^m) (ih (m+1) hm)
      rw [← Nat.pow_add] at hpow
      rw [show m+1+m=2*m+1 by omega] at hpow
      rw [ho]
      exact Nat.le_trans hodd hpow

end Bertrand
