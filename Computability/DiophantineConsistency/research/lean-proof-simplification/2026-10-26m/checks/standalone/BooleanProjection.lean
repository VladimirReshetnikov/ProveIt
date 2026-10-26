import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

namespace AdditionalProofSimplifications

theorem conditional_certificate_vector (Z : ℕ → ℕ → ℕ → Prop)
    (hZ : ∀ b n, (∃ s, Z b n s) ↔ b = if n = 0 then 1 else 0)
    (out n a b : ℕ) :
    (∃ w : Fin 2 → ℕ, Z (w 0) n (w 1) ∧
      (out : ℤ) - ((w 0 : ℤ) * a + (1 - (w 0 : ℤ)) * b) = 0) ↔
      out = if n = 0 then a else b := by
  by_cases hn : n = 0 <;>
    simp [Fin.exists_fin_succ_pi, exists_and_right, hZ, hn, sub_eq_zero]

#print axioms conditional_certificate_vector

end AdditionalProofSimplifications
