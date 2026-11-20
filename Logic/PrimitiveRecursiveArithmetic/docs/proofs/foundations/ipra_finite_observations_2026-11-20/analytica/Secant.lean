import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Rational two-component secant estimate. The points may be arbitrary
rational samples. Input error budgets include any rounding slacks. -/

namespace RationalSecants

abbrev Vec := ℚ × ℚ

def length (v : Vec) : ℚ := |v.1| + |v.2|

def scale (h : ℚ) (v : Vec) : Vec := (h*v.1, h*v.2)

theorem length_add (v w : Vec) :
    length (v+w) ≤ length v + length w := by
  change |v.1 + w.1| + |v.2 + w.2| ≤ (|v.1| + |v.2|) + (|w.1| + |w.2|)
  linarith [abs_add_le v.1 w.1, abs_add_le v.2 w.2]

theorem length_neg (v : Vec) : length (-v) = length v := by
  simp [length]

theorem length_scale (h : ℚ) (hh : 0 ≤ h) (v : Vec) :
    length (scale h v) = h * length v := by
  simp [length, scale, abs_mul, abs_of_nonneg hh, mul_add]

/-- The bottom and top edge samples at x and y differ by at most u.
Both derivative proposals approximate their own scaled first difference
to within the residual budget r. -/
theorem secant_transport (h u r : ℚ) (hh : 0 ≤ h)
    (x₀ x₁ y₀ y₁ d e : Vec)
    (rx : length (x₁-x₀-scale h d) ≤ r)
    (ry : length (y₁-y₀-scale h e) ≤ r)
    (leftEdge : length (x₀-y₀) ≤ u)
    (rightEdge : length (x₁-y₁) ≤ u) :
    h * length (d-e) ≤ 2*r+2*u := by
  let a := -(x₁-x₀-scale h d)
  let b := x₁-y₁
  let c := -(x₀-y₀)
  let f := y₁-y₀-scale h e
  have identity : scale h (d-e) = a+b+c+f := by
    apply Prod.ext <;> simp [scale, a, b, c, f] <;> ring
  have ha : length a ≤ r := by simpa [a, length_neg] using rx
  have hc : length c ≤ u := by simpa [c, length_neg] using leftEdge
  rw [← length_scale h hh, identity]
  linarith [length_add a b, length_add (a+b) c, length_add (a+b+c) f,
    show length b ≤ u from rightEdge, show length f ≤ r from ry]

end RationalSecants
