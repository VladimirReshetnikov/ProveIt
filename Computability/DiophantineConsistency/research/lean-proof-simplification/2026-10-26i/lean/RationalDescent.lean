import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

namespace ProofSimplification.RationalDescent

/-- An integral nonzero power makes the original rational witness integral. -/
theorem num_cast_of_pow_eq_int {q : ℚ} {a : ℤ} {n : ℕ}
    (hn : n ≠ 0) (h : q ^ n = (a : ℚ)) : (q.num : ℚ) = q := by
  apply Rat.coe_int_num_of_den_eq_one
  apply (pow_eq_one_iff_left hn).mp
  simpa only [Rat.den_pow, Rat.den_intCast] using congrArg Rat.den h

/-- Descend the already chosen roots and preserve their linear relation. -/
theorem descend_two_roots {theta omega a b w : ℤ} {r s : ℚ}
    (ho : (omega : ℚ) ≠ 0) (hr : r ^ 2 = (a : ℚ)) (hs : s ^ 2 = (b : ℚ))
    (h : (theta : ℚ) / omega = r + w * s) :
    ∃ r s : ℤ, r ^ 2 = a ∧ s ^ 2 = b ∧ theta = omega * (r + w * s) := by
  have er := num_cast_of_pow_eq_int (by decide : 2 ≠ 0) hr
  have es := num_cast_of_pow_eq_int (by decide : 2 ≠ 0) hs
  rw [← er] at hr h
  rw [← es] at hs h
  refine ⟨r.num, s.num, ?_, ?_, ?_⟩
  · exact_mod_cast hr
  · exact_mod_cast hs
  · exact_mod_cast ((div_eq_iff ho).mp h).trans (mul_comm _ _)

#print axioms num_cast_of_pow_eq_int
#print axioms descend_two_roots
end ProofSimplification.RationalDescent
