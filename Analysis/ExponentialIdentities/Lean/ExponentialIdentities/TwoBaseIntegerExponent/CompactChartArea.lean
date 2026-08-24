import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Compact-chart area certificates

On the logistic (Farey) compactification of the two-power curve, a marked (unit-gap)
point has coordinates `(m/(m+1), n/(n+1))` with `m = 2^t`, `n = 3^t` at a conditional
solution `t`.  The oriented area of three marked points is a rational number with an
*integer numerator* over the product of the six unit denominators:

* `area_eq_div` — the exact identity `Δ = D / ∏ (mᵢ+1)(nᵢ+1)` with an explicit integer `D`;
* `abs_area_ge` — hence `|Δ| ≥ 1/∏ (mᵢ+1)(nᵢ+1)` as soon as `D ≠ 0` (three genuinely
  non-collinear marked points);
* `coord_diff` — the chart spacing identity `m_j/(m_j+1) - m_i/(m_i+1)
  = (m_j - m_i)/((m_i+1)(m_j+1))`;
* `codimension_lock` — the arithmetic form of the coefficient–codimension lock for the
  2026 relation-counting theorem: for `n ≥ 2`, the inequality `(n-1)² < n` (equivalently
  `n - 2 < √n - 1`) holds exactly for `n = 2`, so the natural two-coordinate arithmetic
  event is admissible only in the plane, where polynomial vector fields cannot be tangent
  to the power curve.

The strict concavity of the chart (which makes `Δ < 0`, hence `D ≠ 0`, for genuine curve
points) and the second divided-difference upper bound are analytic and stay outside the
kernel; the arithmetic ledger above is what the three-point certificate consumes.
-/

namespace LeanProofs.TwoBaseIntegerExponent.CompactChart

/-- Oriented area (twice the signed triangle area) of three planar points. -/
def area (x₁ y₁ x₂ y₂ x₃ y₃ : ℚ) : ℚ :=
  (x₂ - x₁) * (y₃ - y₁) - (x₃ - x₁) * (y₂ - y₁)

/-- The integer numerator of the marked three-point area: the `3 × 3` determinant of the
rows `((mᵢ+1)(nᵢ+1), nᵢ+1, mᵢ+1)`, expanded. -/
def areaNum (m₁ n₁ m₂ n₂ m₃ n₃ : ℤ) : ℤ :=
  (m₁ + 1) * (n₁ + 1) * ((n₂ + 1) * (m₃ + 1) - (n₃ + 1) * (m₂ + 1))
    - (n₁ + 1) * ((m₂ + 1) * (n₂ + 1) * (m₃ + 1) - (m₃ + 1) * (n₃ + 1) * (m₂ + 1))
    + (m₁ + 1) * ((m₂ + 1) * (n₂ + 1) * (n₃ + 1) - (m₃ + 1) * (n₃ + 1) * (n₂ + 1))

/-- **Marked-point chart spacing.**  `m_j/(m_j+1) - m_i/(m_i+1)
= (m_j - m_i)/((m_i+1)(m_j+1))`. -/
theorem coord_diff (mi mj : ℕ) :
    (mj : ℚ) / (mj + 1) - (mi : ℚ) / (mi + 1)
      = ((mj : ℚ) - mi) / ((mi + 1) * (mj + 1)) := by
  have hi : ((mi : ℚ) + 1) ≠ 0 := by positivity
  have hj : ((mj : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- **Integer-numerator identity for the marked three-point area.**  For unit-gap
coordinates `Xᵢ = mᵢ/(mᵢ+1)`, `Yᵢ = nᵢ/(nᵢ+1)`,
`Δ = D / ∏ᵢ (mᵢ+1)(nᵢ+1)` with the integer `D = areaNum …`. -/
theorem area_eq_div (m₁ n₁ m₂ n₂ m₃ n₃ : ℕ) :
    area ((m₁ : ℚ) / (m₁ + 1)) ((n₁ : ℚ) / (n₁ + 1))
         ((m₂ : ℚ) / (m₂ + 1)) ((n₂ : ℚ) / (n₂ + 1))
         ((m₃ : ℚ) / (m₃ + 1)) ((n₃ : ℚ) / (n₃ + 1))
      = (areaNum m₁ n₁ m₂ n₂ m₃ n₃ : ℤ) /
          (((m₁ : ℚ) + 1) * ((n₁ : ℚ) + 1) * (((m₂ : ℚ) + 1) * ((n₂ : ℚ) + 1))
            * (((m₃ : ℚ) + 1) * ((n₃ : ℚ) + 1))) := by
  have h₁ : ((m₁ : ℚ) + 1) ≠ 0 := by positivity
  have h₂ : ((n₁ : ℚ) + 1) ≠ 0 := by positivity
  have h₃ : ((m₂ : ℚ) + 1) ≠ 0 := by positivity
  have h₄ : ((n₂ : ℚ) + 1) ≠ 0 := by positivity
  have h₅ : ((m₃ : ℚ) + 1) ≠ 0 := by positivity
  have h₆ : ((n₃ : ℚ) + 1) ≠ 0 := by positivity
  unfold area areaNum
  push_cast
  field_simp
  ring

/-- **Unit-gap area floor.**  If the integer numerator is nonzero, the marked three-point
area is at least the reciprocal of the product of the six unit denominators. -/
theorem abs_area_ge (m₁ n₁ m₂ n₂ m₃ n₃ : ℕ)
    (hD : areaNum m₁ n₁ m₂ n₂ m₃ n₃ ≠ 0) :
    1 / (((m₁ : ℚ) + 1) * ((n₁ : ℚ) + 1) * (((m₂ : ℚ) + 1) * ((n₂ : ℚ) + 1))
          * (((m₃ : ℚ) + 1) * ((n₃ : ℚ) + 1)))
      ≤ |area ((m₁ : ℚ) / (m₁ + 1)) ((n₁ : ℚ) / (n₁ + 1))
              ((m₂ : ℚ) / (m₂ + 1)) ((n₂ : ℚ) / (n₂ + 1))
              ((m₃ : ℚ) / (m₃ + 1)) ((n₃ : ℚ) / (n₃ + 1))| := by
  have hden : (0:ℚ) < ((m₁ : ℚ) + 1) * ((n₁ : ℚ) + 1)
      * (((m₂ : ℚ) + 1) * ((n₂ : ℚ) + 1)) * (((m₃ : ℚ) + 1) * ((n₃ : ℚ) + 1)) := by
    positivity
  have hD1 : (1:ℚ) ≤ |(areaNum m₁ n₁ m₂ n₂ m₃ n₃ : ℚ)| := by
    have h1 : (1:ℤ) ≤ |areaNum m₁ n₁ m₂ n₂ m₃ n₃| := Int.one_le_abs hD
    calc (1:ℚ) = ((1:ℤ) : ℚ) := by norm_num
      _ ≤ ((|areaNum m₁ n₁ m₂ n₂ m₃ n₃| : ℤ) : ℚ) := by exact_mod_cast h1
      _ = |(areaNum m₁ n₁ m₂ n₂ m₃ n₃ : ℚ)| := by push_cast; rfl
  rw [area_eq_div, abs_div, abs_of_pos hden]
  gcongr

/-- **The coefficient–codimension lock.**  For an ambient dimension `n ≥ 2`, the
relation-counting range `k < √n - 1` admits the codimension-two event (`k = n - 2`)
exactly when `n = 2`: in squared form, `(n-1)² < n ↔ n = 2`. -/
theorem codimension_lock {n : ℕ} (hn : 2 ≤ n) : (n - 1) ^ 2 < n ↔ n = 2 := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have he : (m + 3 - 1) ^ 2 = m * m + 4 * m + 4 := by
      have h2 : m + 3 - 1 = m + 2 := by omega
      rw [h2]; ring
    rw [he] at h
    linarith [Nat.zero_le (m * m)]
  · rintro rfl
    norm_num

end LeanProofs.TwoBaseIntegerExponent.CompactChart
