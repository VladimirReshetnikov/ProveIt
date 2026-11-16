import Mathlib.Tactic.Ring

/-!
# Finite algebraic kernel for constructive spherical trigonometry

This file is intended as a Mathlib-level prototype.  It contains only
coordinate polynomial identities; no real completeness, choice, inverse
trigonometric function, or object-language iPRA derivation is used.

STATUS: not compiler-checked in the artifact-building environment, because no
Lean executable was installed there.  There are no `sorry` declarations and no
new axioms.
-/

namespace SphericalIPRA

@[ext] structure V3 (R : Type*) where
  x : R
  y : R
  z : R

namespace V3

variable {R : Type*} [CommRing R]

def zero : V3 R := ⟨0, 0, 0⟩
def add (u v : V3 R) : V3 R := ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩
def neg (u : V3 R) : V3 R := ⟨-u.x, -u.y, -u.z⟩
def sub (u v : V3 R) : V3 R := add u (neg v)
def scale (a : R) (u : V3 R) : V3 R := ⟨a * u.x, a * u.y, a * u.z⟩
def dot (u v : V3 R) : R := u.x * v.x + u.y * v.y + u.z * v.z
def cross (u v : V3 R) : V3 R :=
  ⟨u.y * v.z - u.z * v.y,
   u.z * v.x - u.x * v.z,
   u.x * v.y - u.y * v.x⟩
def det3 (u v w : V3 R) : R := dot u (cross v w)
def sqNorm (u : V3 R) : R := dot u u

theorem add_assoc (u v w : V3 R) : add (add u v) w = add u (add v w) := by
  ext <;> simp [add]

theorem add_comm (u v : V3 R) : add u v = add v u := by
  ext <;> simp [add, add_comm]

theorem add_neg (u : V3 R) : add u (neg u) = zero := by
  ext <;> simp [add, neg, zero]

theorem cross_self (u : V3 R) : cross u u = zero := by
  ext <;> simp [cross, zero] <;> ring

theorem dot_cross_left (u v : V3 R) : dot u (cross u v) = 0 := by
  simp only [dot, cross]
  ring

theorem dot_cross_right (u v : V3 R) : dot v (cross u v) = 0 := by
  simp only [dot, cross]
  ring

/-- Lagrange's identity in bilinear form. -/
theorem lagrange (u v w : V3 R) :
    dot (cross u v) (cross u w) =
      dot u u * dot v w - dot u v * dot u w := by
  simp only [dot, cross]
  ring

/-- The square of the scalar triple product is the 3x3 Gram determinant. -/
theorem gram_det_sq (u v w : V3 R) :
    det3 u v w ^ 2 =
      dot u u * dot v v * dot w w
      + 2 * dot u v * dot v w * dot w u
      - dot u u * dot v w ^ 2
      - dot v v * dot w u ^ 2
      - dot w w * dot u v ^ 2 := by
  simp only [det3, dot, cross]
  ring

/-- Numerator form of polar involution. -/
theorem polar_double_cross (u v w : V3 R) :
    cross (cross w u) (cross u v) = scale (det3 w u v) u := by
  ext <;> simp only [cross, scale, det3, dot] <;> ring

/-- Squared norm of a sum of three vectors. -/
theorem sqNorm_add3 (u v w : V3 R) :
    sqNorm (add (add u v) w) =
      sqNorm u + sqNorm v + sqNorm w
      + 2 * dot u v + 2 * dot u w + 2 * dot v w := by
  simp only [sqNorm, dot, add]
  ring

/-- Coordinate face-area vectors of a tetrahedron sum to zero. -/
def face1 (a b c : V3 R) : V3 R := neg (cross b c)
def face2 (a b c : V3 R) : V3 R := neg (cross c a)
def face3 (a b c : V3 R) : V3 R := neg (cross a b)
def face4 (a b c : V3 R) : V3 R :=
  add (add (cross b c) (cross c a)) (cross a b)

theorem face_area_closure (a b c : V3 R) :
    add (add (add (face1 a b c) (face2 a b c)) (face3 a b c))
      (face4 a b c) = zero := by
  ext <;> simp only [face1, face2, face3, face4, add, neg, zero, cross] <;> ring

end V3

section ScalarKernel

variable {R : Type*} [CommRing R]

/-- The Gram factorization behind the unit angle pair. -/
theorem angle_pair_numerator
    (x y z tau : R)
    (hgram : tau ^ 2 = 1 + 2*x*y*z - x^2 - y^2 - z^2) :
    (x - y*z)^2 + tau^2 = (1 - y^2) * (1 - z^2) := by
  rw [hgram]
  ring

/-- Polynomial numerator identity for the supplemental cosine law. -/
theorem supplemental_cosine_numerator
    (x y z tau : R)
    (hgram : tau ^ 2 = 1 + 2*x*y*z - x^2 - y^2 - z^2) :
    -(y - z*x) * (z - x*y) + x*tau^2 =
      (1 - x^2) * (x - y*z) := by
  rw [hgram]
  ring

/-- The solid-angle normalization identity. -/
theorem solid_angle_norm (x y z tau : R)
    (hgram : tau ^ 2 = 1 + 2*x*y*z - x^2 - y^2 - z^2) :
    (1 + x + y + z)^2 + tau^2 =
      2 * (1+x) * (1+y) * (1+z) := by
  rw [hgram]
  ring

end ScalarKernel

end SphericalIPRA

-- Suggested audits after compilation:
-- #print axioms SphericalIPRA.V3.gram_det_sq
-- #print axioms SphericalIPRA.V3.face_area_closure
-- #print axioms SphericalIPRA.supplemental_cosine_numerator
