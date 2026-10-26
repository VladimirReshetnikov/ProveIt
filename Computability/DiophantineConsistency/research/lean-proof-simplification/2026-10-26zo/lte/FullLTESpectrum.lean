import Mathlib.NumberTheory.Multiplicity
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
A standalone, proof-only prototype of a stronger API for PrimePowerOrder.
The first three helper statements reproduce the maintained source prerequisites;
the proposed contribution starts at `lift_dvd_iff`.
-/
namespace DiophantineConsistency.Research.FullLTESpectrum

set_option Elab.async false
set_option maxRecDepth 10000

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

/-- Full divisibility spectrum: the exponent need not be a prime power.
The zero exponent is included because emultiplicity p 0 = top. -/
theorem lift_dvd_iff {p g : ℕ} (hp : Nat.Prime p) (ho : Odd p)
    (hd : p ∣ g-1) (hs : ¬ p^2 ∣ g-1) (k m : ℕ) :
    p^(k+1) ∣ g^m-1 ↔ p^k ∣ m := by
  have hnd := not_dvd_of_dvd_sub_one hp (one_lt_of_not_square hs).le hd
  have hbase : emultiplicity p (g-1) = (1 : ℕ) :=
    emultiplicity_eq_coe.mpr (by simpa only [pow_one] using And.intro hd hs)
  have hv : emultiplicity p (g^m-1) = 1+emultiplicity p m := by
    simpa only [one_pow, hbase, Nat.cast_one] using
      Nat.emultiplicity_pow_sub_pow hp ho hd hnd m
  rw [pow_dvd_iff_le_emultiplicity, hv, pow_dvd_iff_le_emultiplicity,
    Nat.cast_add, Nat.cast_one, add_comm (k : ℕ∞) 1,
    ENat.add_le_add_iff_left (by simp)]

/-- One rewrite decides when any power is one at the selected modulus. -/
theorem pow_eq_one_iff {p g : ℕ} (hp : Nat.Prime p) (ho : Odd p)
    (hd : p ∣ g-1) (hs : ¬ p^2 ∣ g-1) (k m : ℕ) :
    (g : ZMod (p^(k+1)))^m = 1 ↔ p^k ∣ m :=
  (pow_cast_eq_one_iff (one_lt_of_not_square hs).le m).trans
    (lift_dvd_iff hp ho hd hs k m)

/-- Exact order follows from equality of divisibility predicates;
there is no split on k, including at the modulus p itself. -/
theorem order_succ {p g : ℕ} (hp : Nat.Prime p) (ho : Odd p)
    (hd : p ∣ g-1) (hs : ¬ p^2 ∣ g-1) (k : ℕ) :
    orderOf (g : ZMod (p^(k+1))) = p^k := by
  have h (m : ℕ) : orderOf (g : ZMod (p^(k+1))) ∣ m ↔ p^k ∣ m := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_eq_one_iff hp ho hd hs]
  exact Nat.dvd_antisymm ((h (p^k)).mpr dvd_rfl) ((h _).mp dvd_rfl)

/-- The former exact-lift API is retained as a corollary. -/
theorem exact_lift {p g : ℕ} (hp : Nat.Prime p) (ho : Odd p)
    (hd : p ∣ g-1) (hs : ¬ p^2 ∣ g-1) (k : ℕ) :
    p^(k+1) ∣ g^(p^k)-1 ∧ ¬ p^(k+2) ∣ g^(p^k)-1 := by
  simp [lift_dvd_iff hp ho hd hs, Nat.pow_dvd_pow_iff_le_right hp.one_lt]

#print axioms lift_dvd_iff
#print axioms pow_eq_one_iff
#print axioms order_succ
#print axioms exact_lift

-- The singular exponent m=0 has to remain accepted.
example (k : ℕ) : 3^(k+1) ∣ 4^0-1 ↔ 3^k ∣ 0 :=
  lift_dvd_iff (by decide) (by decide) (by decide) (by decide) k 0

-- The smallest modulus (k=0) gives order 1, without a separate branch.
example : orderOf (4 : ZMod (3^1)) = 1 := by
  simpa using order_succ (by decide : Nat.Prime 3) (by decide)
    (by decide : 3 ∣ 4-1) (by decide : ¬ 3^2 ∣ 4-1) 0

-- A non-prime-power exponent, exercising the genuinely stronger interface.
example : (4 : ZMod (3^3))^18 = 1 :=
  (pow_eq_one_iff (by decide) (by decide) (by decide) (by decide) 2 18).mpr (by decide)
example : (4 : ZMod (3^3))^6 ≠ 1 :=
  fun h => (by decide : ¬ 3^2 ∣ 6)
    ((pow_eq_one_iff (by decide) (by decide) (by decide) (by decide) 2 6).mp h)

end DiophantineConsistency.Research.FullLTESpectrum
