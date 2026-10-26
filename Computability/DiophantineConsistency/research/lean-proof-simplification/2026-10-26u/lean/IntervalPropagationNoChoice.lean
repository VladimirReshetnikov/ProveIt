import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Init

namespace NewWangSimplification

theorem interval_propagate (P : ℤ → Prop) (l r x₀ : ℤ)
    (hl₀ : l < x₀) (hr₀ : x₀ < r) (h₀ : P x₀)
    (hnext : ∀ x, l < x → x+1 < r → P x → P (x+1))
    (hprev : ∀ x, l < x-1 → x < r → P x → P (x-1)) :
    ∀ x, l < x → x < r → P x := by
  have shifted (z : ℤ) : l < x₀ + z → x₀ + z < r → P (x₀ + z) := by
    induction z using Int.induction_on with
    | zero => exact fun _ _ => (show P (x₀ + 0) from (by simpa only [add_zero] using h₀))
    | succ n ih =>
        intro hl hr
        simpa only [add_assoc] using
          hnext (x₀ + (n : ℤ)) (by omega) (by omega) (ih (by omega) (by omega))
    | pred n ih =>
        intro hl hr
        simpa only [add_sub_assoc] using
          hprev (x₀ + -(n : ℤ)) (by omega) (by omega) (ih (by omega) (by omega))
  intro x hl hr
  have he : x₀ + (x - x₀) = x := by omega
  simpa only [he] using shifted (x-x₀) (by omega) (by omega)

#print axioms interval_propagate
end NewWangSimplification
