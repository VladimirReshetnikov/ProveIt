import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

theorem list_weighted_error_sum {α : Type*} (xs : List α) (P m e : α → ℝ) (C : ℝ)
    (h : ∀ x ∈ xs, P x ≤ C * m x + e x) :
    (xs.map P).sum ≤ C * (xs.map m).sum + (xs.map e).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons]
    nlinarith

theorem list_weighted_error_sum_le {α : Type*} (xs : List α) (P m e : α → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hm : (xs.map m).sum ≤ 1) (h : ∀ x ∈ xs, P x ≤ C * m x + e x) :
    (xs.map P).sum ≤ C + (xs.map e).sum := by
  have hs := list_weighted_error_sum xs P m e C h
  have hc := mul_le_mul_of_nonneg_left hm hC
  nlinarith

end Erdos3

end

end OAI
