import Mathlib.Tactic.Ring

/-!
# The finite polynomial kernel of Rodrigues' formula

STATUS: proposed Lean 4 / Mathlib v4.32.0 source, not compiler-checked in the
authoring environment (no Lean installation was available). There are no
`sorry` declarations and no new axioms. This file is an algebraic prototype;
it is NOT an object-language iPRA derivation.

All statements are identities in a commutative ring. In particular, none uses
real completeness, a spectral theorem, trigonometry, or choice of an axis.
-/

namespace ConstructiveRotation

@[ext] structure V3 (R : Type*) where
  x : R
  y : R
  z : R

namespace V3

variable {R : Type*} [CommRing R]

def add (v w : V3 R) : V3 R := ⟨v.x + w.x, v.y + w.y, v.z + w.z⟩
def scale (a : R) (v : V3 R) : V3 R := ⟨a * v.x, a * v.y, a * v.z⟩
def dot (v w : V3 R) : R := v.x * w.x + v.y * w.y + v.z * w.z
def cross (v w : V3 R) : V3 R :=
  ⟨v.y * w.z - v.z * w.y, v.z * w.x - v.x * w.z,
    v.x * w.y - v.y * w.x⟩

def basisX : V3 R := ⟨1, 0, 0⟩
def basisY : V3 R := ⟨0, 1, 0⟩
def basisZ : V3 R := ⟨0, 0, 1⟩

/-- Determinant of the matrix with the displayed three columns. -/
def detCols (a b c : V3 R) : R := dot a (cross b c)

/-- Rodrigues' expression with a circle-valued angle `(c,s)`. -/
def rodrigues (u : V3 R) (c s : R) (v : V3 R) : V3 R :=
  add (add (scale c v) (scale s (cross u v)))
    (scale ((1 - c) * dot u v) u)

theorem scale_one (v : V3 R) : scale 1 v = v := by
  apply V3.ext <;> simp [scale]

theorem cross_self (v : V3 R) : cross v v = ⟨0, 0, 0⟩ := by
  apply V3.ext <;> simp [cross] <;> ring

theorem dot_cross_left (u v : V3 R) : dot u (cross u v) = 0 := by
  simp only [dot, cross]
  ring

theorem dot_cross_right (u v : V3 R) : dot v (cross u v) = 0 := by
  simp only [dot, cross]
  ring

theorem cross_cross (u v : V3 R) :
    cross u (cross u v) =
      add (scale (dot u v) u) (scale (-dot u u) v) := by
  apply V3.ext <;> simp only [cross, add, scale, dot] <;> ring

theorem lagrange (u v w : V3 R) :
    dot (cross u v) (cross u w) =
      dot u u * dot v w - dot u v * dot u w := by
  simp only [dot, cross]
  ring

theorem rodrigues_on_axis (u : V3 R) (c s : R) :
    rodrigues u c s u = scale (c + (1 - c) * dot u u) u := by
  apply V3.ext <;> simp only [rodrigues, add, scale, cross, dot] <;> ring

theorem rodrigues_fixes_unit_axis (u : V3 R) (c s : R)
    (hu : dot u u = 1) : rodrigues u c s u = u := by
  rw [rodrigues_on_axis, hu]
  have hc : c + (1 - c) * (1 : R) = 1 := by ring
  rw [hc, scale_one]

/-- Dot-product identity before either normalization hypothesis is imposed. -/
theorem rodrigues_dot (u v w : V3 R) (c s : R) :
    dot (rodrigues u c s v) (rodrigues u c s w) =
      (c * c + s * s * dot u u) * dot v w +
      ((1 - c) * (1 - c) * dot u u + 2 * c * (1 - c) - s * s) *
        dot u v * dot u w := by
  simp only [rodrigues, dot, add, scale, cross]
  ring

theorem rodrigues_preserves_dot (u v w : V3 R) (c s : R)
    (hu : dot u u = 1) (hcs : c * c + s * s = 1) :
    dot (rodrigues u c s v) (rodrigues u c s w) = dot v w := by
  rw [rodrigues_dot]
  simp only [hu, mul_one]
  have hzero : (1 - c) * (1 - c) +
      2 * c * (1 - c) - s * s = 0 := by
    calc
      _ = 1 - (c * c + s * s) := by ring
      _ = 0 := by rw [hcs]; ring
  rw [hcs, hzero]
  ring

/-- The determinant identity is valid without assuming `dot u u = 1`. -/
theorem rodrigues_det (u : V3 R) (c s : R) :
    detCols (rodrigues u c s basisX) (rodrigues u c s basisY)
      (rodrigues u c s basisZ) =
      (c + (1 - c) * dot u u) * (c * c + s * s * dot u u) := by
  simp only [detCols, rodrigues, basisX, basisY, basisZ, add, scale, cross, dot]
  ring

theorem rodrigues_det_one (u : V3 R) (c s : R)
    (hu : dot u u = 1) (hcs : c * c + s * s = 1) :
    detCols (rodrigues u c s basisX) (rodrigues u c s basisY)
      (rodrigues u c s basisZ) = 1 := by
  rw [rodrigues_det]
  simp only [hu, mul_one, hcs]
  ring

/-- A single coordinate identity sufficient for the Rodrigues reconstruction. -/
theorem rodrigues_coordinate_x (u v : V3 R) (c s : R) :
    (rodrigues u c s v).x =
      c * v.x + s * (u.y * v.z - u.z * v.y) +
        (1 - c) * (u.x * v.x + u.y * v.y + u.z * v.z) * u.x := by
  rfl

end V3
end ConstructiveRotation

/- Run these after compilation to inspect the dependencies of the actual
kernel proof terms:

#print axioms ConstructiveRotation.V3.rodrigues_preserves_dot
#print axioms ConstructiveRotation.V3.rodrigues_det_one

This audit is useful but does not replace construction of a
ConciseIPRA.Prf derivation for the arithmetized theorem.
-/
