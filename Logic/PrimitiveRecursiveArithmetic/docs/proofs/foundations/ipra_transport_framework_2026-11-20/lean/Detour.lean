import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Rational inequalities used in the five-segment detour. A fixed forbidden
integer is arbitrary; the clearance result is therefore simultaneous in all
integer translates. All norms use real and imaginary coordinate maxima. -/
namespace ParameterDetour

def gapAt (real imag : ℚ) (level : ℤ) : ℚ :=
  max |real - (level : ℚ)| |imag|

private theorem absAfterMove (a b : ℚ) : |a| ≤ |b| + |a - b| := by
  calc
    |a| = |b + (a - b)| := by ring_nf
    _ ≤ |b| + |a - b| := abs_add_le _ _

/-- Perturbing both coordinates of a parameter value by at most ε loses
at most ε in clearance. This handles short endpoint segments and boxes. -/
theorem clearanceAfterMove {r i s j ε γ : ℚ} (n : ℤ)
    (start : γ ≤ gapAt r i n) (hr : |r - s| ≤ ε) (hi : |i - j| ≤ ε) :
    γ - ε ≤ gapAt s j n := by
  have ar := absAfterMove (r - (n : ℚ)) (s - (n : ℚ))
  have diff : (r - (n : ℚ)) - (s - (n : ℚ)) = r - s := by ring
  rw [diff] at ar
  have ai := absAfterMove i j
  have ur : |s - (n : ℚ)| ≤ gapAt s j n := le_max_left _ _
  have ui : |j| ≤ gapAt s j n := le_max_right _ _
  have both : gapAt r i n ≤ gapAt s j n + ε :=
    max_le (by linarith only [ar, hr, ur]) (by linarith only [ai, hi, ui])
  linarith only [start, both]

/-- Once the shifted real part has a gap, arbitrary vertical motion is safe. -/
theorem verticalSeparated {q u η i : ℚ} (n : ℤ)
    (old : η ≤ |q - (n : ℚ)|) (small : |u| ≤ η/4) :
    3*η/4 ≤ gapAt (q + u) i n := by
  have h := absAfterMove (q - (n : ℚ)) (q + u - (n : ℚ))
  have diff : (q - (n : ℚ)) - (q + u - (n : ℚ)) = -u := by ring
  rw [diff, abs_neg] at h
  have hr : |q + u - (n : ℚ)| ≤ gapAt (q+u) i n := le_max_left _ _
  linarith only [old, small, h, hr]

private theorem distinctIntegerGap {q n : ℤ} (hne : q ≠ n) :
    (1 : ℚ) ≤ |(q : ℚ) - (n : ℚ)| := by
  rcases lt_or_gt_of_ne hne with h | h
  · have h1 : (q : ℚ) + 1 ≤ (n : ℚ) := by exact_mod_cast (show q + 1 ≤ n by omega)
    rw [abs_of_nonpos (by linarith only [h1])]
    linarith only [h1]
  · have h1 : (n : ℚ) + 1 ≤ (q : ℚ) := by exact_mod_cast (show n + 1 ≤ q by omega)
    rw [abs_of_nonneg (by linarith only [h1])]
    linarith only [h1]

/-- With integral starting real part a shift of magnitude at most 1/4 keeps
a gap of at least its own magnitude from every integer level. -/
theorem verticalInteger (q n : ℤ) (u i : ℚ) (small : |u| ≤ 1/4) :
    |u| ≤ gapAt ((q : ℚ) + u) i n := by
  by_cases h : q = n
  · subst q
    unfold gapAt
    simpa only [add_sub_cancel_left] using (le_max_left |(n : ℚ) + u - n| |i|)
  · have far := verticalSeparated (η := 1) (q := (q : ℚ)) (i := i) n
        (distinctIntegerGap h) small
    linarith only [small, far]

/-- The horizontal segment at fixed imaginary height uses no real-part test. -/
theorem middle (real imag γ : ℚ) (n : ℤ) (height : γ ≤ |imag|) :
    γ ≤ gapAt real imag n :=
  height.trans (le_max_right _ _)

end ParameterDetour
