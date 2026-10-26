import Mathlib.NumberTheory.Multiplicity
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

/-! Exact order of a first-order principal unit modulo odd prime powers.
The positivity and unit conditions are derived from the stated divisibility
assumptions; no orbit enumeration or CRT property is assumed. -/
namespace DiophantineConsistency.PrimePowerOrderBaseline

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
  have hk : 1 ≤ g^k := one_le_pow₀ hg
  constructor
  · intro h
    apply (CharP.cast_eq_zero_iff (ZMod m) m (g^k-1)).mp
    rw [Nat.cast_sub hk, Nat.cast_pow, Nat.cast_one, h, sub_self]
  · intro h
    have hz := (CharP.cast_eq_zero_iff (ZMod m) m (g^k-1)).mpr h
    rw [Nat.cast_sub hk, Nat.cast_pow, Nat.cast_one] at hz
    exact sub_eq_zero.mp hz

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

end DiophantineConsistency.PrimePowerOrderBaseline
#print axioms DiophantineConsistency.PrimePowerOrderBaseline.one_lt_of_not_square
#print axioms DiophantineConsistency.PrimePowerOrderBaseline.not_dvd_of_dvd_sub_one
#print axioms DiophantineConsistency.PrimePowerOrderBaseline.pow_cast_eq_one_iff
#print axioms DiophantineConsistency.PrimePowerOrderBaseline.exact_lift
#print axioms DiophantineConsistency.PrimePowerOrderBaseline.order_succ
#print axioms DiophantineConsistency.PrimePowerOrderBaseline.order_prime_power

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
  have hk : 1 ≤ g^k := one_le_pow₀ hg
  constructor
  · intro h
    apply (CharP.cast_eq_zero_iff (ZMod m) m (g^k-1)).mp
    rw [Nat.cast_sub hk, Nat.cast_pow, Nat.cast_one, h, sub_self]
  · intro h
    have hz := (CharP.cast_eq_zero_iff (ZMod m) m (g^k-1)).mpr h
    rw [Nat.cast_sub hk, Nat.cast_pow, Nat.cast_one] at hz
    exact sub_eq_zero.mp hz

/-- LTE as a divisibility normal form, for every exponent including zero. -/
theorem lift_divisibility {p g : ℕ} (hp : Nat.Prime p) (ho : Odd p)
    (hd : p ∣ g-1) (hs : ¬ p^2 ∣ g-1) (n k : ℕ) :
    p^(n+1) ∣ g^k-1 ↔ p^n ∣ k := by
  have hg := one_lt_of_not_square hs
  have hnd := not_dvd_of_dvd_sub_one hp hg.le hd
  have hbase : emultiplicity p (g-1) = (1 : ℕ) :=
    emultiplicity_eq_coe.mpr (by simpa only [pow_one] using And.intro hd hs)
  have hv : emultiplicity p (g^k-1) = 1+emultiplicity p k := by
    simpa only [one_pow, hbase, Nat.cast_one] using Nat.emultiplicity_pow_sub_pow hp ho hd hnd k
  rw [pow_dvd_iff_le_emultiplicity, hv, pow_dvd_iff_le_emultiplicity,
    Nat.cast_add, Nat.cast_one, add_comm (1 : ℕ∞),
    ENat.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)]

/-- LTE gives exact valuation k+1, not merely a divisibility lower bound. -/
theorem exact_lift {p g : ℕ} (hp : Nat.Prime p) (ho : Odd p)
    (hd : p ∣ g-1) (hs : ¬ p^2 ∣ g-1) (k : ℕ) :
    p^(k+1) ∣ g^(p^k)-1 ∧ ¬ p^(k+2) ∣ g^(p^k)-1 := by
  simp [lift_divisibility hp ho hd hs, Nat.pow_dvd_pow_iff_le_right hp.one_lt]

/-- The modulus p is included: the order is p^0=1. -/
theorem order_succ {p g : ℕ} (hp : Nat.Prime p) (ho : Odd p)
    (hd : p ∣ g-1) (hs : ¬ p^2 ∣ g-1) (k : ℕ) :
    orderOf (g : ZMod (p^(k+1))) = p^k := by
  have hg := (one_lt_of_not_square hs).le
  apply Nat.dvd_antisymm
  · rw [orderOf_dvd_iff_pow_eq_one, pow_cast_eq_one_iff hg,
      lift_divisibility hp ho hd hs]
  · rw [← lift_divisibility hp ho hd hs k,
      ← pow_cast_eq_one_iff hg]
    exact pow_orderOf_eq_one _

theorem order_prime_power {p g n : ℕ} (hp : Nat.Prime p) (ho : Odd p)
    (hd : p ∣ g-1) (hs : ¬ p^2 ∣ g-1) (hn : 1 ≤ n) :
    orderOf (g : ZMod (p^n)) = p^(n-1) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using order_succ hp ho hd hs k

end DiophantineConsistency.PrimePowerOrder

namespace DiophantineConsistency.PrimePowerOrderChecks

open PrimePowerOrder
set_option Elab.async false

-- The base modulus has order1, not p.
example : orderOf (4 : ZMod (3^1)) = 1 := by
  simpa using order_prime_power (p:=3) (g:=4) (n:=1)
    (by decide) (by decide) (by decide) (by decide) (by decide)

example : orderOf (4 : ZMod (3^3)) = 9 := by
  simpa using order_prime_power (p:=3) (g:=4) (n:=3)
    (by decide) (by decide) (by decide) (by decide) (by decide)

example (k : ℕ) : 3^(k+1) ∣ 4^(3^k)-1 ∧ ¬ 3^(k+2) ∣ 4^(3^k)-1 :=
  exact_lift (by decide) (by decide) (by decide) (by decide) k

-- Natural subtraction at g=0 or1 cannot satisfy the nontrivial lift.
example (p : ℕ) : p^2 ∣ (0 : ℕ)-1 := by simp
example (p : ℕ) : p^2 ∣ (1 : ℕ)-1 := by simp

-- The odd-prime hypothesis matters:3 modulo8 has order2, not4.
example : orderOf (3 : ZMod 8) = 2 := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  exact orderOf_eq_prime (by decide) (by decide)
example : 2 ∣ (3 : ℕ)-1 ∧ ¬ 2^2 ∣ (3 : ℕ)-1 := by decide

-- A lift divisible by p² may instead have order1 already modulo p².
example : orderOf (10 : ZMod 9) = 1 :=
  orderOf_eq_one_iff.mpr (by decide)
example : 3^2 ∣ (10 : ℕ)-1 := by decide

-- The generic cast bridge includes exponent0 and even modulus0.
example : (4 : ZMod 0)^0 = 1 ↔ (0 : ℕ) ∣ 4^0-1 :=
  pow_cast_eq_one_iff (by decide) 0

#print axioms one_lt_of_not_square
#print axioms not_dvd_of_dvd_sub_one
#print axioms pow_cast_eq_one_iff
#print axioms exact_lift
#print axioms order_succ
#print axioms order_prime_power

end DiophantineConsistency.PrimePowerOrderChecks

namespace DiophantineConsistency.PrimePowerOrderAdditionalChecks
open PrimePowerOrder
example (n : ℕ) : 3^(n+1) ∣ 4^0-1 ↔ 3^n ∣ 0 :=
  lift_divisibility (by decide) (by decide) (by decide) (by decide) n 0
example : 3^(1+1) ∣ 4^6-1 ↔ 3^1 ∣ 6 :=
  lift_divisibility (by decide) (by decide) (by decide) (by decide) 1 6
#print axioms lift_divisibility
end DiophantineConsistency.PrimePowerOrderAdditionalChecks
