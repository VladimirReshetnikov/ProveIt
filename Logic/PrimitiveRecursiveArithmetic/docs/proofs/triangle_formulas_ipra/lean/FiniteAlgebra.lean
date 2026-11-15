import Mathlib.Tactic

/-!
# The finite polynomial kernel of the three triangle formulas

STATUS: proposed Lean proof scripts, not compiled in the delivery environment
(neither Lean nor Lake was installed).  No theorem in this file is a claim of
derivability in the embedded theory `ConciseIPRA.PRAAx`.

These identities require only a commutative ring.  Their use with rational
coordinates, and their eventual replay in iPRA, are explained in the report.
The same dot/determinant route is already used by ProveIt's
`Algebra/SurrealNumbers/Surreal/Algebra/Geometry.lean`, inspected at commit
38cafaa5be7f4602567440bcebc754abdbacefc9.  Here the coordinates and the additional
circumcenter numerators are exposed directly to minimize dependencies.
-/

namespace TriangleIPRA

section Ring

variable {R : Type*} [CommRing R]

def normSq (x y : R) : R := x ^ 2 + y ^ 2

def dot (x y z w : R) : R := x * z + y * w

def det (x y z w : R) : R := x * w - y * z

def sideSq (x y z w : R) : R := (x - z) ^ 2 + (y - w) ^ 2

/-- The cosine law before division by the side lengths. -/
theorem cosine_polynomial (x y z w : R) :
    sideSq x y z w = normSq x y + normSq z w - 2 * dot x y z w := by
  simp only [sideSq, normSq, dot]
  ring

/-- The two-dimensional Gram identity. -/
theorem gram (x y z w : R) :
    normSq x y * normSq z w = (dot x y z w) ^ 2 + (det x y z w) ^ 2 := by
  simp only [normSq, dot, det]
  ring

/-- Heron's symmetric polynomial in the three squared side lengths. -/
theorem heron_coordinates (x y z w : R) :
    2 * (sideSq x y z w * normSq z w + normSq z w * normSq x y +
      normSq x y * sideSq x y z w) -
      (sideSq x y z w) ^ 2 - (normSq z w) ^ 2 - (normSq x y) ^ 2 =
      4 * (det x y z w) ^ 2 := by
  simp only [sideSq, normSq, det]
  ring

/-- Heron's factorization, with no square-root or order assumptions. -/
theorem heron_factorization (a b c : R) :
    (a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c) =
      2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) -
        (a ^ 2) ^ 2 - (b ^ 2) ^ 2 - (c ^ 2) ^ 2 := by
  ring

/-- The alternative factorization useful for a short handwritten proof. -/
theorem heron_factorization_gram (a b c : R) :
    (a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c) =
      4 * b ^ 2 * c ^ 2 - (b ^ 2 + c ^ 2 - a ^ 2) ^ 2 := by
  ring

/-- Any specified square roots of the squared sides satisfy Heron's product. -/
theorem heron_from_squared_lengths (a b c x y z w : R)
    (ha : a ^ 2 = sideSq x y z w)
    (hb : b ^ 2 = normSq z w)
    (hc : c ^ 2 = normSq x y) :
    (a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c) =
      4 * (det x y z w) ^ 2 := by
  rw [heron_factorization, ha, hb, hc]
  exact heron_coordinates x y z w

/-- First numerator of the circumcenter, whose denominator is `2 * det`. -/
def centerNumX (x y z w : R) : R := normSq x y * w - normSq z w * y

/-- Second numerator of the circumcenter. -/
def centerNumY (x y z w : R) : R := normSq z w * x - normSq x y * z

theorem center_dot_u (x y z w : R) :
    x * centerNumX x y z w + y * centerNumY x y z w =
      normSq x y * det x y z w := by
  simp only [centerNumX, centerNumY, normSq, det]
  ring

theorem center_dot_v (x y z w : R) :
    z * centerNumX x y z w + w * centerNumY x y z w =
      normSq z w * det x y z w := by
  simp only [centerNumX, centerNumY, normSq, det]
  ring

/-- The identity giving `R = abc / (2 * |det|)` after positive square roots. -/
theorem center_norm (x y z w : R) :
    (centerNumX x y z w) ^ 2 + (centerNumY x y z w) ^ 2 =
      sideSq x y z w * normSq x y * normSq z w := by
  simp only [centerNumX, centerNumY, sideSq, normSq]
  ring

/-- Equidistance from the origin and `u`, with denominators cleared. -/
theorem center_equidistant_u (x y z w : R) :
    (centerNumX x y z w - 2 * det x y z w * x) ^ 2 +
      (centerNumY x y z w - 2 * det x y z w * y) ^ 2 =
      (centerNumX x y z w) ^ 2 + (centerNumY x y z w) ^ 2 := by
  simp only [centerNumX, centerNumY, normSq, det]
  ring

/-- Equidistance from the origin and `v`, with denominators cleared. -/
theorem center_equidistant_v (x y z w : R) :
    (centerNumX x y z w - 2 * det x y z w * z) ^ 2 +
      (centerNumY x y z w - 2 * det x y z w * w) ^ 2 =
      (centerNumX x y z w) ^ 2 + (centerNumY x y z w) ^ 2 := by
  simp only [centerNumX, centerNumY, normSq, det]
  ring

/-- The signed doubled areas at the other two vertices. -/
theorem vertex_determinants (x y z w : R) :
    det (-x) (-y) (z - x) (w - y) = -det x y z w ∧
    det (-z) (-w) (x - z) (y - w) = det x y z w := by
  constructor <;> simp only [det] <;> ring

/-- The real numerator when the first two unit angle pairs are multiplied. -/
theorem two_angle_real_numerator (x y z w : R) :
    dot x y z w * (normSq x y - dot x y z w) - (det x y z w) ^ 2 =
      normSq x y * (dot x y z w - normSq z w) := by
  simp only [dot, normSq, det]
  ring

/-- The imaginary numerator of the same product; `h` denotes `|det|`. -/
theorem two_angle_imag_numerator (u p h : R) :
    h * p + h * (u - p) = h * u := by
  ring

end Ring

end TriangleIPRA
