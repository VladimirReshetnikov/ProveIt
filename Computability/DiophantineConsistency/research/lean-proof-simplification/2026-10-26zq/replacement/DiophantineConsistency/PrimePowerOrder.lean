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
  have hk : 1 ≤ g^k := one_le_pow₀ hg
  constructor
  · intro h
    apply (CharP.cast_eq_zero_iff (ZMod m) m (g^k-1)).mp
    rw [Nat.cast_sub hk, Nat.cast_pow, Nat.cast_one, h, sub_self]
  · intro h
    have hz := (CharP.cast_eq_zero_iff (ZMod m) m (g^k-1)).mpr h
    rw [Nat.cast_sub hk, Nat.cast_pow, Nat.cast_one] at hz
    exact sub_eq_zero.mp hz

/-- LTE describes every exponent, including m=0. -/
theorem pow_divisibility {p g : ℕ} (hp : Nat.Prime p) (ho : Odd p)
    (hd : p ∣ g-1) (hs : ¬ p^2 ∣ g-1) (k m : ℕ) :
    p^(k+1) ∣ g^m-1 ↔ p^k ∣ m := by
  have hg := one_lt_of_not_square hs
  have hnd := not_dvd_of_dvd_sub_one hp hg.le hd
  have hbase : emultiplicity p (g-1) = (1 : ℕ) :=
    emultiplicity_eq_coe.mpr (by simpa only [pow_one] using And.intro hd hs)
  have hv := Nat.emultiplicity_pow_sub_pow hp ho hd hnd m
  simp only [one_pow, hbase] at hv
  rw [pow_dvd_iff_le_emultiplicity, pow_dvd_iff_le_emultiplicity, hv,
    Nat.cast_add, Nat.cast_one, add_comm (k : ℕ∞) 1]
  exact ENat.add_le_add_iff_left (by simp)

/-- The previous exact-lift endpoint is retained. -/
theorem exact_lift {p g : ℕ} (hp : Nat.Prime p) (ho : Odd p)
    (hd : p ∣ g-1) (hs : ¬ p^2 ∣ g-1) (k : ℕ) :
    p^(k+1) ∣ g^(p^k)-1 ∧ ¬ p^(k+2) ∣ g^(p^k)-1 := by
  refine ⟨(pow_divisibility hp ho hd hs k _).mpr dvd_rfl, ?_⟩
  rw [show k+2 = (k+1)+1 by omega, pow_divisibility hp ho hd hs]
  rw [Nat.pow_dvd_pow_iff_le_right hp.one_lt]
  omega

/-- The same two divisibilities establish order at every k, including zero. -/
theorem order_succ {p g : ℕ} (hp : Nat.Prime p) (ho : Odd p)
    (hd : p ∣ g-1) (hs : ¬ p^2 ∣ g-1) (k : ℕ) :
    orderOf (g : ZMod (p^(k+1))) = p^k := by
  have hpow (m : ℕ) : (g : ZMod (p^(k+1)))^m = 1 ↔ p^k ∣ m :=
    (pow_cast_eq_one_iff (one_lt_of_not_square hs).le m).trans
      (pow_divisibility hp ho hd hs k m)
  exact Nat.dvd_antisymm
    (orderOf_dvd_of_pow_eq_one ((hpow _).mpr dvd_rfl))
    ((hpow _).mp (pow_orderOf_eq_one _))

theorem order_prime_power {p g n : ℕ} (hp : Nat.Prime p) (ho : Odd p)
    (hd : p ∣ g-1) (hs : ¬ p^2 ∣ g-1) (hn : 1 ≤ n) :
    orderOf (g : ZMod (p^n)) = p^(n-1) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using order_succ hp ho hd hs k

end DiophantineConsistency.PrimePowerOrder
