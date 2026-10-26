import DiophantineConsistency.PrimePowerOrder

namespace ProofSimplification.PrimePowerAnnihilator

open DiophantineConsistency.PrimePowerOrder

/-- LTE describes the entire annihilator of the principal unit, including
m=0, where both divisibilities hold. -/
theorem dvd_pow_sub_one_iff {p g : ℕ} (hp : Nat.Prime p) (ho : Odd p)
    (hd : p ∣ g - 1) (hs : ¬ p ^ 2 ∣ g - 1) (k m : ℕ) :
    p ^ (k + 1) ∣ g ^ m - 1 ↔ p ^ k ∣ m := by
  have hg := one_lt_of_not_square hs
  have hnd := not_dvd_of_dvd_sub_one hp hg.le hd
  have hbase : emultiplicity p (g - 1) = (1 : ℕ) :=
    emultiplicity_eq_coe.mpr (by simpa only [pow_one] using And.intro hd hs)
  have hv := Nat.emultiplicity_pow_sub_pow hp ho hd hnd m
  simp only [one_pow, hbase] at hv
  rw [pow_dvd_iff_le_emultiplicity, pow_dvd_iff_le_emultiplicity, hv,
    Nat.cast_add, Nat.cast_one, add_comm (k : ℕ∞) 1]
  exact ENat.add_le_add_iff_left (by simp)

theorem pow_eq_one_iff {p g : ℕ} (hp : Nat.Prime p) (ho : Odd p)
    (hd : p ∣ g - 1) (hs : ¬ p ^ 2 ∣ g - 1) (k m : ℕ) :
    (g : ZMod (p ^ (k + 1))) ^ m = 1 ↔ p ^ k ∣ m :=
  (pow_cast_eq_one_iff (one_lt_of_not_square hs).le m).trans
    (dvd_pow_sub_one_iff hp ho hd hs k m)

/-- Exact order follows from the two divisibilities, uniformly at k=0. -/
theorem order_uniform {p g : ℕ} (hp : Nat.Prime p) (ho : Odd p)
    (hd : p ∣ g - 1) (hs : ¬ p ^ 2 ∣ g - 1) (k : ℕ) :
    orderOf (g : ZMod (p ^ (k + 1))) = p ^ k := by
  apply Nat.dvd_antisymm
  · exact orderOf_dvd_of_pow_eq_one ((pow_eq_one_iff hp ho hd hs k _).mpr dvd_rfl)
  · exact (pow_eq_one_iff hp ho hd hs k _).mp (pow_orderOf_eq_one _)

#print axioms dvd_pow_sub_one_iff
#print axioms pow_eq_one_iff
#print axioms order_uniform

end ProofSimplification.PrimePowerAnnihilator
