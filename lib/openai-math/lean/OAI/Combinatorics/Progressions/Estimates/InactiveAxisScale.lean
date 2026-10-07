import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

noncomputable def inactiveSideLength (h K q : ℕ) : ℕ :=
  if 2 * q ≤ K then Nat.nthRoot h (K / q) else 1

def inactivePrincipalCoefficient (K q : ℕ) : ℤ := if 2 * q ≤ K then 1 else 0

theorem inactiveSideLength_pos {h K q : ℕ} (hh : 0 < h) (hq : 0 < q) :
    0 < inactiveSideLength h K q := by
  by_cases hlarge : 2 * q ≤ K
  · have hdiv : 2 ≤ K / q := (Nat.le_div_iff_mul_le hq).mpr hlarge
    have hroot : 1 ≤ Nat.nthRoot h (K / q) :=
      (Nat.le_nthRoot_iff hh.ne').mpr (by simpa only [one_pow] using (by omega : 1 ≤ K / q))
    simpa [inactiveSideLength, hlarge, Nat.succ_le_iff] using hroot
  · simp [inactiveSideLength, hlarge]

theorem inactiveSideLength_power {h K q : ℕ} (hh : 0 < h) (hlarge : 2 * q ≤ K) :
    inactiveSideLength h K q ^ h ≤ K / q := by
  simpa [inactiveSideLength, hlarge] using (Nat.pow_nthRoot_le (.inl hh.ne') : Nat.nthRoot h (K / q) ^ h ≤ K / q)

theorem inactiveSideLength_le {h K q L : ℕ} (hh : 0 < h) (hL : 0 < L)
    (hK : K ≤ L ^ h) : inactiveSideLength h K q ≤ L := by
  by_cases hlarge : 2 * q ≤ K
  · apply (Nat.pow_left_strictMono hh.ne').le_iff_le.mp
    exact (inactiveSideLength_power hh hlarge).trans ((Nat.div_le_self K q).trans hK)
  · simpa [inactiveSideLength, hlarge] using (show 1 ≤ L by omega)

theorem inactiveSideLength_lower_power {h K q : ℕ} (hh : 0 < h) (hq : 0 < q)
    (hlarge : 2 * q ≤ K) : K < q * 2 ^ h * inactiveSideLength h K q ^ h := by
  have hpos := inactiveSideLength_pos (K := K) hh hq
  have hnext : K / q < (inactiveSideLength h K q + 1) ^ h := by
    simpa [inactiveSideLength, hlarge] using Nat.lt_pow_nthRoot_add_one hh.ne' (K / q)
  have hdiv : K < q * (K / q + 1) := by
    have hm := Nat.mod_lt K hq
    have he := Nat.mod_add_div K q
    nlinarith
  calc
    K < q * (K / q + 1) := hdiv
    _ ≤ q * (inactiveSideLength h K q + 1) ^ h :=
      Nat.mul_le_mul_left q (Nat.succ_le_of_lt hnext)
    _ ≤ q * (2 * inactiveSideLength h K q) ^ h := by gcongr; omega
    _ = _ := by rw [mul_pow]; ring

theorem inactivePrincipal_small {K q : ℕ} (hsmall : K < 2 * q) :
    inactivePrincipalCoefficient K q = 0 := by
  simp [inactivePrincipalCoefficient, not_le.mpr hsmall]

theorem inactivePrincipal_large {K q : ℕ} (hlarge : 2 * q ≤ K) :
    inactivePrincipalCoefficient K q = 1 := by
  simp [inactivePrincipalCoefficient, hlarge]

end Erdos3

end

end OAI
