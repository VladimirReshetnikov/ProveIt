import Mathlib

namespace OAI

section

namespace Erdos3

open scoped Pointwise

theorem higher_difference_card_le {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) (hA : A.Nonempty) {K : ℝ}
    (hsmall : ((A - A).card : ℝ) ≤ K * A.card) (m n : ℕ) :
    ((m • A - n • A).card : ℝ) ≤ K ^ (m + n) * A.card := by
  have h := Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_sub hA A m n
  have hreal : ((m • A - n • A).card : ℝ) ≤
      (((A - A).card : ℝ) / A.card) ^ (m + n) * A.card := by
    have hc := (NNRat.cast_le (K := ℝ)).mpr h
    simpa only [NNRat.cast_natCast, NNRat.cast_mul, NNRat.cast_pow,
      NNRat.cast_div] using hc
  have hcard : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hratio : ((A - A).card : ℝ) / A.card ≤ K :=
    (div_le_iff₀ hcard).mpr hsmall
  exact hreal.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity) hratio _) hcard.le)

end Erdos3

end

end OAI
