import Std.Tactic

/-! Finite integer core of dyadic derivative reconstruction. The surrounding
analytic and object-theory statements are developed in chapters/case.tex. -/
namespace DyadicDetail

def Band (radius value : Int) : Prop :=
  -radius ≤ value ∧ value ≤ radius

/-- At one fixed reading precision, the difference of the two child slopes
controls the discrepancy of either child from the parent. Multiplication by
the common positive denominator and by the half-cell width is understood. -/
theorem childFromSecondDifference (left mid right radius : Int)
    (h : Band radius (right - 2 * mid + left)) :
    Band radius (2 * (mid - left) - (right - left)) ∧
    Band radius (2 * (right - mid) - (right - left)) := by
  rcases h with ⟨hlo, hhi⟩
  constructor <;> constructor <;> omega

/-- Quantization of consecutive values perturbs a second difference by at
most four times their common error. -/
theorem secondDifferenceNoise (a b c x y z e : Int)
    (ha : Band e (a - x)) (hb : Band e (b - y)) (hc : Band e (c - z)) :
    Band (4 * e) ((a - 2 * b + c) - (x - 2 * y + z)) := by
  rcases ha with ⟨ha₁, ha₂⟩
  rcases hb with ⟨hb₁, hb₂⟩
  rcases hc with ⟨hc₁, hc₂⟩
  constructor <;> omega

theorem addBudget (a b e f : Int) (ha : Band e a) (hb : Band f b) :
    Band (e + f) (a + b) := by
  rcases ha with ⟨ha₁, ha₂⟩
  rcases hb with ⟨hb₁, hb₂⟩
  constructor <;> omega

/-- Numerator identity giving curvature constant 2 for rational samples of
the square function on a common dyadic denominator. -/
theorem squareGridDetail (j : Int) :
    (j + 2) * (j + 2) - 2 * ((j + 1) * (j + 1)) + j * j = 2 := by
  simp only [Int.add_mul, Int.mul_add]
  omega

end DyadicDetail
