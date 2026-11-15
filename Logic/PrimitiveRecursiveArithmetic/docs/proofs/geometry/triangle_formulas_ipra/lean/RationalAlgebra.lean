import Mathlib.Tactic

/-!
# Rational denominator-clearing lemmas

STATUS: proposed proof scripts, not compiled in this environment.  These
host-Lean statements are algebraic checks, not embedded iPRA derivations.
No analytic real-number library is used.  The separate finite polynomial
kernel works over every commutative ring; these normalization lemmas are
specialized to the rationals to keep the side conditions explicit.
-/

namespace TriangleIPRA

/-- The normalization used for all three geometric sine values. -/
theorem sine_over_side (a b c t : ℚ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (t / (b * c)) / a = t / (a * b * c) := by
  field_simp [ha, hb, hc] <;> ring

/-- The familiar side-over-sine form needs a nonzero doubled area. -/
theorem side_over_sine (a b c t : ℚ)
    (hb : b ≠ 0) (hc : c ≠ 0) (ht : t ≠ 0) :
    a / (t / (b * c)) = a * b * c / t := by
  field_simp [hb, hc, ht] <;> ring

/-- Twice the explicit positive circumradius. -/
theorem twice_radius (a b c t : ℚ) (ht : t ≠ 0) :
    2 * (a * b * c / (2 * t)) = a * b * c / t := by
  field_simp [ht] <;> ring

/-- Conversion of the projection identity to the usual cosine-law notation. -/
theorem cosine_division (b c d : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) :
    b ^ 2 + c ^ 2 - 2 * d =
      b ^ 2 + c ^ 2 - 2 * b * c * (d / (b * c)) := by
  field_simp [hb, hc] <;> ring

/-- The four factors after introduction of the semiperimeter. -/
theorem semiperimeter_product (a b c : ℚ) :
    16 * ((a + b + c) / 2) * (((a + b + c) / 2) - a) *
      (((a + b + c) / 2) - b) * (((a + b + c) / 2) - c) =
      (a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c) := by
  ring

/-- A quantitative square-root estimate using only ordered rational arithmetic. -/
theorem square_difference_bound (r s e : ℚ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (he : 0 ≤ e)
    (h : |r ^ 2 - s ^ 2| ≤ e ^ 2) :
    |r - s| ≤ e := by
  apply (sq_le_sq₀ (abs_nonneg _) he).mp
  simp only [sq_abs]
  by_cases hrs : r ≤ s
  · have hsq : r ^ 2 ≤ s ^ 2 := (sq_le_sq₀ hr hs).mpr hrs
    have hp : 0 ≤ r * (s - r) := mul_nonneg hr (sub_nonneg.mpr hrs)
    rw [abs_of_nonpos (sub_nonpos.mpr hsq)] at h
    nlinarith
  · have hsr : s ≤ r := le_of_lt (lt_of_not_ge hrs)
    have hsq : s ^ 2 ≤ r ^ 2 := (sq_le_sq₀ hs hr).mpr hsr
    have hp : 0 ≤ s * (r - s) := mul_nonneg hs (sub_nonneg.mpr hsr)
    rw [abs_of_nonneg (sub_nonneg.mpr hsq)] at h
    nlinarith

end TriangleIPRA
