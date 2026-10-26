import Mathlib.NumberTheory.Multiplicity
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

/-! Exact order of a first-order principal unit modulo odd prime powers.
The positivity and unit conditions are derived from the stated divisibility
assumptions; no orbit enumeration or CRT property is assumed. -/
namespace DiophantineConsistency.PrimePowerOrder

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem one_lt_of_not_square {p g : ℕ} (h : ¬ p^2 ∣ g-1) : 1 < g := by
  by_contra hn
  have hz : g-1 = 0 := by omega
  exact h (hz ▸ dvd_zero _)

theorem not_dvd_of_dvd_sub_one {p g : ℕ} (hp : Nat.Prime p)
    (hg : 1 ≤ g) (hd : p ∣ g-1) : ¬ p ∣ g := by
  intro h
  have hh := Nat.dvd_sub h hd
  have he : g-(g-1) = 1 := by omega
  exact hp.not_dvd_one (he ▸ hh)

/-- Natural subtraction is used only after proving the needed lower bound. -/
theorem pow_cast_eq_one_iff {g m : ℕ} (hg : 1 ≤ g) (k : ℕ) :
    (g : ZMod m)^k = 1 ↔ m ∣ g^k-1 := by
  rw [← CharP.cast_eq_zero_iff (ZMod m) m (g^k-1),
    Nat.cast_sub (one_le_pow₀ hg), Nat.cast_pow, Nat.cast_one, sub_eq_zero]

/-- LTE gives exact valuation k+1, not merely a divisibility lower bound. -/
theorem exact_lift {p g : ℕ} (hp : Nat.Prime p) (ho : Odd p)
    (hd : p ∣ g-1) (hs : ¬ p^2 ∣ g-1) (k : ℕ) :
    p^(k+1) ∣ g^(p^k)-1 ∧ ¬ p^(k+2) ∣ g^(p^k)-1 := by
  have hg := one_lt_of_not_square hs
  have hnd := not_dvd_of_dvd_sub_one hp hg.le hd
  have hbase : emultiplicity p (g-1) = (1 : ℕ) :=
    emultiplicity_eq_coe.mpr (by simpa only [pow_one] using And.intro hd hs)
  have hval := Nat.emultiplicity_pow_sub_pow hp ho hd hnd (p^k)
  have hv : emultiplicity p (g^(p^k)-1) = ((k+1 : ℕ) : ℕ∞) := by
    simpa only [one_pow, hbase, emultiplicity_pow_self_of_prime hp.prime,
      Nat.cast_add, Nat.cast_one, add_comm] using hval
  simpa only [Nat.add_assoc] using (emultiplicity_eq_coe.mp hv)

/-- The modulus p is included: the order is p^0=1. -/
theorem order_succ {p g : ℕ} (hp : Nat.Prime p) (ho : Odd p)
    (hd : p ∣ g-1) (hs : ¬ p^2 ∣ g-1) (k : ℕ) :
    orderOf (g : ZMod (p^(k+1))) = p^k := by
  letI : Fact p.Prime := ⟨hp⟩
  have hg := (one_lt_of_not_square hs).le
  cases k with
  | zero =>
      rw [pow_zero]
      apply orderOf_eq_one_iff.mpr
      have h := (pow_cast_eq_one_iff (m:=p^(0+1)) hg 1).mpr (by simpa using hd)
      simpa only [pow_one] using h
  | succ k =>
      apply orderOf_eq_prime_pow (p:=p) (n:=k)
      · rw [pow_cast_eq_one_iff hg]
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using
          (exact_lift hp ho hd hs k).2
      · rw [pow_cast_eq_one_iff hg]
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using
          (exact_lift hp ho hd hs (k+1)).1

theorem order_prime_power {p g n : ℕ} (hp : Nat.Prime p) (ho : Odd p)
    (hd : p ∣ g-1) (hs : ¬ p^2 ∣ g-1) (hn : 1 ≤ n) :
    orderOf (g : ZMod (p^n)) = p^(n-1) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using order_succ hp ho hd hs k

end DiophantineConsistency.PrimePowerOrder
