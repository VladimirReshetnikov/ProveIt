import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

namespace AdditionalProofSimplifications

/-- Existentially hide the second component of an invertible code. -/
theorem exists_pair_right_iff (z a : ℕ) :
    (∃ b, z = Nat.pair a b) ↔ a = (Nat.unpair z).1 := by
  constructor
  · rintro ⟨b, rfl⟩
    simp
  · intro h
    exact ⟨(Nat.unpair z).2, by rw [h, Nat.pair_unpair]⟩

/-- Existentially hide the first component of an invertible code. -/
theorem exists_pair_left_iff (z b : ℕ) :
    (∃ a, z = Nat.pair a b) ↔ b = (Nat.unpair z).2 := by
  constructor
  · rintro ⟨a, rfl⟩
    simp
  · intro h
    exact ⟨(Nat.unpair z).1, by rw [h, Nat.pair_unpair]⟩

variable (C : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Prop)
  (hc : ∀ z a b, (∃ t s m, C z a b t s m) ↔ z = Nat.pair a b)

include hc

/-- All graph clients use the same certificate elimination theorem. -/
theorem pair_certificate_vector (z a b : ℕ) :
    (∃ w : Fin 3 → ℕ, C z a b (w 0) (w 1) (w 2)) ↔ z = Nat.pair a b := by
  simpa [Fin.exists_fin_succ_pi] using hc z a b

theorem left_certificate_vector (z a : ℕ) :
    (∃ w : Fin 4 → ℕ, C z a (w 0) (w 1) (w 2) (w 3)) ↔
      a = (Nat.unpair z).1 := by
  simp [Fin.exists_fin_succ_pi, hc, exists_pair_right_iff]

theorem right_certificate_vector (z b : ℕ) :
    (∃ w : Fin 4 → ℕ, C z (w 0) b (w 1) (w 2) (w 3)) ↔
      b = (Nat.unpair z).2 := by
  simp [Fin.exists_fin_succ_pi, hc, exists_pair_left_iff]

theorem tree_left_certificate_vector (z a : ℕ) :
    (∃ w : Fin 5 → ℕ, w 0 = z.pred ∧ C (w 0) a (w 1) (w 2) (w 3) (w 4)) ↔
      a = (Nat.unpair z.pred).1 := by
  simp [Fin.exists_fin_succ_pi, exists_and_left, hc, exists_pair_right_iff]

theorem tree_right_certificate_vector (z b : ℕ) :
    (∃ w : Fin 5 → ℕ, w 0 = z.pred ∧ C (w 0) (w 1) b (w 2) (w 3) (w 4)) ↔
      b = (Nat.unpair z.pred).2 := by
  simp [Fin.exists_fin_succ_pi, exists_and_left, hc, exists_pair_left_iff]

#print axioms exists_pair_right_iff
#print axioms left_certificate_vector
#print axioms tree_left_certificate_vector

end AdditionalProofSimplifications
