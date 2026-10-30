import Mathlib.Data.List.GetD

/-! Conditional lookup of appended and repeated lists. -/
namespace DiophantineConsistency.ListGetDCases

theorem append {α : Type*} (a b : List α) (d : α) (j : ℕ) :
    (a ++ b).getD j d = if j < a.length then a.getD j d else b.getD (j-a.length) d := by
  by_cases h : j < a.length
  · simp only [if_pos h]; exact List.getD_append a b d j h
  · simp only [if_neg h]; exact List.getD_append_right a b d j (Nat.le_of_not_gt h)

theorem replicate {α : Type*} (n : ℕ) (x d : α) (j : ℕ) :
    (List.replicate n x).getD j d = if j < n then x else d := by
  by_cases h : j < n
  · simp only [if_pos h]; exact List.getD_replicate x h
  · simp only [if_neg h]; exact List.getD_eq_default (List.replicate n x) d (by
      simpa only [List.length_replicate] using Nat.le_of_not_gt h)

end DiophantineConsistency.ListGetDCases
