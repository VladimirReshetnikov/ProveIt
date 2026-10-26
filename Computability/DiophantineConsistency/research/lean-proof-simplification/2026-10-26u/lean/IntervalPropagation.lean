import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Init

namespace NewWangSimplification

theorem interval_propagate (P : ℤ → Prop) (l r x₀ : ℤ)
    (hl₀ : l < x₀) (hr₀ : x₀ < r) (h₀ : P x₀)
    (hnext : ∀ x, l < x → x+1 < r → P x → P (x+1))
    (hprev : ∀ x, l < x-1 → x < r → P x → P (x-1)) :
    ∀ x, l < x → x < r → P x := by
  intro x
  induction x using Int.inductionOn' (b := x₀) with
  | zero => exact fun _ _ => h₀
  | succ k hk ih =>
      intro hl hr
      exact hnext k (by omega) hr (ih (by omega) (by omega))
  | pred k hk ih =>
      intro hl hr
      exact hprev k hl (by omega) (ih (by omega) (by omega))

#print axioms interval_propagate
end NewWangSimplification
