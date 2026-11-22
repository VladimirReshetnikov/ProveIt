import Mathlib

/-!
# Finite algebra for cuboid-surface geodesics

This file isolates polynomial/rational identities used by the paper.  It is
intended to be checked with the ProveIt root toolchain (Lean 4 / Mathlib).  The
current execution environment did not contain `lean` or `lake`, so this file
has not been elaborated here.  It contains no `sorry`.
-/

namespace CuboidSurface

noncomputable section

variable (A B C x y : ℝ)

def L0Sq : ℝ := (A + B) ^ 2 + C ^ 2

def d1Sq : ℝ := (A + C) ^ 2 + (B - 2 * y) ^ 2

def d2Sq : ℝ := (B + C) ^ 2 + (A - 2 * x) ^ 2

def d3Sq : ℝ := (C + x + y) ^ 2 + (A + B - x - y) ^ 2

def d4Sq : ℝ := (A + B) ^ 2 + (C + 2 * y) ^ 2

def d5Sq : ℝ := (A + B) ^ 2 + (C + 2 * x) ^ 2

def q1 : ℝ :=
  (x + (C - A) / 2) * (y + (C - B) / 2) - (C ^ 2 - A * B) / 4

def q2 : ℝ :=
  (y - B / 2) ^ 2 - (x - A / 2) ^ 2 -
    (B - A) * (A + B + 2 * C) / 4

/-- The third unfolding depends only on `x+y`; this factorization detects
when it beats the opposite-vertex value. -/
theorem d3_gap :
    d3Sq A B C x y - L0Sq A B C =
      2 * (x + y) * (C - A - B + x + y) := by
  simp only [d3Sq, L0Sq]
  ring

/-- The two hyperbolas used to locate the triple balancing point. -/
theorem q1_identity :
    (2 * d3Sq A B C x y - d1Sq A B C y - d2Sq A B C x) / 8 =
      q1 A B C x y := by
  simp only [d1Sq, d2Sq, d3Sq, q1]
  ring

theorem q2_identity :
    (d1Sq A B C y - d2Sq A B C x) / 4 = q2 A B C x y := by
  simp only [d1Sq, d2Sq, q2]
  ring

/-- Cross-multiplied forms of the inequalities showing that unfoldings 4 and
5 are nonbinding at the triple balancing point. -/
theorem d2_d5_gap :
    d2Sq A B C x - d5Sq A B C x =
      -4 * (A + C) * x + 2 * B * (C - A) := by
  simp only [d2Sq, d5Sq]
  ring

theorem d1_d4_gap :
    d1Sq A B C y - d4Sq A B C y =
      -4 * (B + C) * y + 2 * A * (C - B) := by
  simp only [d1Sq, d4Sq]
  ring

/-- Algebra for the fixed-vertex candidate. -/
def fixedDelta : ℝ := A * (C - B) / (2 * C)

def fixedR2 : ℝ :=
  (B ^ 2 + C ^ 2) * (A ^ 2 + 2 * A * C + 2 * C ^ 2) / (2 * C ^ 2)

def fixedK : ℝ := 2 * C ^ 2 - 2 * B * C - A * C - A * B

/-- The sign deciding whether the opposite vertex remains farthest. -/
theorem fixed_gap (hC : C ≠ 0) :
    fixedR2 A B C - L0Sq A B C =
      A * (C - B) * fixedK A B C / (2 * C ^ 2) := by
  simp only [fixedR2, L0Sq, fixedK]
  field_simp [hC]
  ring

/-- At `(A-delta,B-delta)` the source images 1, 2, and 4 are equidistant. -/
theorem fixed_source_1 (hC : C ≠ 0) :
    let δ := fixedDelta A B C
    (A - δ + C) ^ 2 + (B - δ) ^ 2 = fixedR2 A B C := by
  simp only [fixedDelta, fixedR2]
  field_simp [hC]
  ring

theorem fixed_source_2 (hC : C ≠ 0) :
    let δ := fixedDelta A B C
    (A - δ - A - C) ^ 2 + (B - δ + A) ^ 2 = fixedR2 A B C := by
  simp only [fixedDelta, fixedR2]
  field_simp [hC]
  ring

theorem fixed_source_4 (hC : C ≠ 0) :
    let δ := fixedDelta A B C
    (A - δ + B) ^ 2 + (B - δ - B - C) ^ 2 = fixedR2 A B C := by
  simp only [fixedDelta, fixedR2]
  field_simp [hC]
  ring

/-- The omitted fourth source is farther by `2*C*(B-A)`. -/
theorem fixed_omitted_source (hC : C ≠ 0) :
    let δ := fixedDelta A B C
    (A - δ) ^ 2 + (B - δ + C) ^ 2 - fixedR2 A B C =
      2 * C * (B - A) := by
  simp only [fixedDelta, fixedR2]
  field_simp [hC]
  ring

/-- Boundary-balancing algebra.  The hypothesis is the defining equation for
`H`; the result is `d1^2=d3^2=D^2`. -/
theorem boundary_balance
    (H : ℝ)
    (hH : H ^ 2 = (B + C) ^ 2 - 2 * A * (C - B) - A ^ 2) :
    let τ := (B + C - H) / 2
    let D2 := B ^ 2 + 3 * C ^ 2 + 2 * B * (A + C) - 2 * C * H
    d1Sq A B C τ = D2 ∧ d3Sq A B C (A / 2) τ = D2 := by
  dsimp [d1Sq, d3Sq]
  constructor <;> nlinarith [hH]

/-- If `u=A-2x` and `v=B-2y`, the third unfolding produces the final radical
in the scalar root equation. -/
theorem root_reconstruction (u v : ℝ) :
    let xi := (A - u) / 2
    let yi := (B - v) / 2
    2 * d3Sq A B C xi yi - (A + B + C) ^ 2 = (C - u - v) ^ 2 := by
  simp only [d3Sq]
  ring

end

end CuboidSurface
