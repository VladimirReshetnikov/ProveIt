import Mathlib.Data.Nat.Find
import Lean.Elab.Tactic.Omega

/-!
# Least failure with its interior and predecessor

The predecessor conclusion is deliberately a disjunction: the first failure
may occur exactly at the starting index, including when that index is zero.
-/

namespace DiophantineConsistency.FirstExit

theorem exists_first_failure (P : ℕ → Prop) [DecidablePred P] (a b : ℕ)
    (hab : a ≤ b) (hb : ¬ P b) :
    ∃ k : ℕ, a ≤ k ∧ k ≤ b ∧ ¬ P k ∧
      (∀ j : ℕ, a ≤ j → j < k → P j) ∧ (k = a ∨ P (k - 1)) := by
  have hex : ∃ j : ℕ, a ≤ j ∧ ¬ P j := ⟨b, hab, hb⟩
  let k := Nat.find hex
  have hk := Nat.find_spec hex
  have hi (j : ℕ) (ha : a ≤ j) (hj : j < k) : P j := by
    by_contra hn
    exact (Nat.find_min hex hj) ⟨ha, hn⟩
  refine ⟨k, hk.1, Nat.find_min' hex ⟨hab, hb⟩, hk.2, hi, ?_⟩
  by_cases hka : k = a
  · exact Or.inl hka
  · exact Or.inr (hi (k - 1) (by omega) (by omega))

end DiophantineConsistency.FirstExit
