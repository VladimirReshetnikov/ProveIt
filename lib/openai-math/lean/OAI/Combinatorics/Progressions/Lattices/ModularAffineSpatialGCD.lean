import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic

namespace OAI

section

namespace Erdos3

theorem nat_gcd_primePower_eq_pow_min_factorization {stride p : ℕ}
    (hstride : 0 < stride) (hp : p.Prime) (a : ℕ) :
    Nat.gcd stride (p ^ a) = p ^ min (stride.factorization p) a := by
  obtain ⟨b, hba, hb⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right stride (p ^ a))
  have hbs : p ^ b ∣ stride := by
    rw [← hb]
    exact Nat.gcd_dvd_left stride (p ^ a)
  have hbval : b ≤ stride.factorization p :=
    (hp.pow_dvd_iff_le_factorization hstride.ne').mp hbs
  apply Nat.dvd_antisymm
  · rw [hb]
    exact pow_dvd_pow p (le_min hbval hba)
  · exact Nat.dvd_gcd
      ((hp.pow_dvd_iff_le_factorization hstride.ne').mpr (min_le_left _ _))
      (pow_dvd_pow p (min_le_right _ _))

theorem zmod_natCast_gcd_primePower_eq_pow_min_factorization {stride p : ℕ}
    (hstride : 0 < stride) (hp : p.Prime) (a : ℕ) :
    Nat.gcd ((stride : ZMod (p ^ a)).val) (p ^ a) =
      p ^ min (stride.factorization p) a := by
  rw [ZMod.val_natCast, ← Nat.gcd_rec, Nat.gcd_comm]
  exact nat_gcd_primePower_eq_pow_min_factorization hstride hp a

end Erdos3

end

end OAI
