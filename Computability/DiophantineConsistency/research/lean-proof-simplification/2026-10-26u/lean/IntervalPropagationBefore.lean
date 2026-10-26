import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Init
namespace BaselineWang
theorem interval_propagate (P : ℤ → Prop) (l r x₀ : ℤ)
    (hl₀ : l < x₀) (hr₀ : x₀ < r) (h₀ : P x₀)
    (hnext : ∀ x, l < x → x+1 < r → P x → P (x+1))
    (hprev : ∀ x, l < x-1 → x < r → P x → P (x-1)) :
    ∀ x, l < x → x < r → P x := by
  have hright (n : ℕ) : x₀+(n : ℤ) < r → P (x₀+(n : ℤ)) := by
    induction n with
    | zero => intro h; simpa only [Nat.cast_zero, add_zero] using h₀
    | succ n ih =>
        intro hb
        have hp := ih (by omega)
        have hs := hnext (x₀+(n : ℤ)) (by omega) (by omega) hp
        have he : x₀+((n+1 : ℕ) : ℤ) = (x₀+(n : ℤ))+1 := by omega
        simpa only [he] using hs
  have hleft (n : ℕ) : l < x₀-(n : ℤ) → P (x₀-(n : ℤ)) := by
    induction n with
    | zero => intro h; simpa only [Nat.cast_zero, sub_zero] using h₀
    | succ n ih =>
        intro hb
        have hp := ih (by omega)
        have hs := hprev (x₀-(n : ℤ)) (by omega) (by omega) hp
        have he : x₀-((n+1 : ℕ) : ℤ) = (x₀-(n : ℤ))-1 := by omega
        simpa only [he] using hs
  intro x hl hr
  by_cases hx : x₀ ≤ x
  · have he : x₀+((x-x₀).toNat : ℤ) = x := by omega
    have hh := hright (x-x₀).toNat (by omega)
    simpa only [he] using hh
  · have he : x₀-((x₀-x).toNat : ℤ) = x := by omega
    have hh := hleft (x₀-x).toNat (by omega)
    simpa only [he] using hh
#print axioms interval_propagate
end BaselineWang
