import Std

/- The finite algebra only. This does not formalize the HC construction or
   a consistency comparison. `decide` is checked by the Lean kernel. -/
namespace FourthParameter

abbrev Value := Fin 4

def imp (a b : Value) : Value :=
  if a = 0 then 3
  else if a = 1 then (if b = 2 then 1 else 3)
  else if a = 2 then 3
  else if b = 3 then 3 else 0

def row (a b c u : Value) : Value :=
  imp (imp (imp c u) a) (imp (imp a c) (imp b c))

theorem failures : ∀ a b c u : Value,
    row a b c u ≠ 3 ↔ (a = 0 ∨ a = 1) ∧ b = 3 ∧ c = 1 ∧ u = 2 := by
  decide

theorem implication_range : ∀ a b : Value, imp a b ≠ 2 := by
  decide

theorem safe_choices : ∀ a b c u : Value,
    (u = 0 ∨ u = 1 ∨ u = 3 ∨ u = a ∨ u = b ∨ u = c) → row a b c u = 3 := by
  decide

theorem detects_colors : row 0 3 1 2 = 0 := by decide

theorem classical_without_one : ∀ a b : Value, a ≠ 1 → b ≠ 1 →
    imp a b ≠ 1 ∧ (imp a b = 3 ↔ (a = 3 → b = 3)) := by
  decide

theorem classical_without_two : ∀ a b : Value, a ≠ 2 → b ≠ 2 →
    imp a b ≠ 2 ∧ (imp a b = 3 ↔ (a = 3 → b = 3)) := by
  decide

/-- An assignment interpretation validating the proposal cannot realize
    both colored nonmembership values. The syntactic instance producing
    this hypothesis is explained in README.md. -/
theorem one_color_absent {D : Type} (r : D → D → Value)
    (valid : ∀ w q z p, row 0 3 (r w q) (r z p) = 3) :
    (∀ w q, r w q ≠ 1) ∨ (∀ z p, r z p ≠ 2) := by
  classical
  by_cases h : ∀ w q, r w q ≠ 1
  · exact Or.inl h
  · right
    have hex : ∃ w q, r w q = 1 := by
      by_contra hn
      apply h
      intro w q he
      exact hn ⟨w, q, he⟩
    obtain ⟨w, q, hwq⟩ := hex
    intro z p hzp
    have hc := valid w q z p
    rw [hwq, hzp] at hc
    have h03 : (0 : Value) = 3 := detects_colors.symm.trans hc
    exact (by decide : (0 : Value) ≠ 3) h03

#print axioms failures
#print axioms implication_range
#print axioms safe_choices
#print axioms detects_colors
#print axioms classical_without_one
#print axioms classical_without_two
#print axioms one_color_absent

end FourthParameter
