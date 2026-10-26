import DiophantineConsistency.PairingProjection
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Fin.Tuple.Basic


namespace DiophantineConsistency.PairingProjection

theorem pair_left (z a : ℕ) :
    (∃ b, z = Nat.pair a b) ↔ a = (Nat.unpair z).1 :=
  exists_right_iff Nat.pairEquiv z a

theorem pair_right (z b : ℕ) :
    (∃ a, z = Nat.pair a b) ↔ b = (Nat.unpair z).2 :=
  exists_left_iff Nat.pairEquiv z b

example (z a : ℕ) :
    (∃ w : Fin 1 → ℕ, z = Nat.pair a (w 0)) ↔ a = (Nat.unpair z).1 := by
  simpa only [Fin.exists_fin_succ_pi, Fin.exists_fin_zero_pi, Fin.cons_zero] using pair_left z a

section Certificate
variable (R : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Prop)
variable (correct : ∀ z a b, (∃ t s m, R z a b t s m) ↔ z = Nat.pair a b)
include correct

-- Exact shape of the quadratic backend's inverse-projection proof obligation.
theorem quadratic_left (z a : ℕ) :
    (∃ w : Fin 4 → ℕ, R z a (w 0) (w 1) (w 2) (w 3)) ↔ a = (Nat.unpair z).1 := by
  simp only [Fin.exists_fin_succ_pi, Fin.exists_fin_zero_pi]
  change (∃ b t s m, R z a b t s m) ↔ _
  simp only [correct]
  exact pair_left z a

theorem tree_left (z a : ℕ) :
    (∃ w : Fin 5 → ℕ, w 0 = z.pred ∧ R (w 0) a (w 1) (w 2) (w 3) (w 4)) ↔
      a = (Nat.unpair z.pred).1 := by
  simp only [Fin.exists_fin_succ_pi, Fin.exists_fin_zero_pi]
  change (∃ p b t s m, p = z.pred ∧ R p a b t s m) ↔ _
  simp only [exists_and_left, exists_eq_left, correct]
  exact pair_left z.pred a

end Certificate

#print axioms exists_right_iff
#print axioms exists_left_iff
#print axioms quadratic_left
#print axioms tree_left
end DiophantineConsistency.PairingProjection
