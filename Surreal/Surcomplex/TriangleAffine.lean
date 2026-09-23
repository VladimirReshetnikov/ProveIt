import Surreal.Surcomplex.TriangleLaws
import Mathlib.LinearAlgebra.AffineSpace.Ceva
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Actual surcomplex triangles as Mathlib affine triangles

The nonzero determinant in the actual triangle definition implies
Mathlib affine independence over the surreal scalar field. This bridge
allows the incidence arguments, including `trigonometry:thm:ceva`, to
reuse the existing affine-geometry theorems at every surreal scale.
-/

universe u

namespace Surreal.Surcomplex.Triangle

open Foundations

noncomputable section

/-- A nonzero actual determinant rules out affine collinearity of the three vertices. -/
theorem not_collinear (T : Triangle.{u}) :
    ¬ Collinear SignSequence.{u} ({T.A, T.B, T.C} : Set Surcomplex.{u}) := by
  intro h
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem
    (by simp : T.A ∈ ({T.A, T.B, T.C} : Set Surcomplex.{u}))).mp h
  obtain ⟨b, hb⟩ := hv T.B (by simp)
  obtain ⟨c, hc⟩ := hv T.C (by simp)
  change T.B = b • v + T.A at hb
  change T.C = c • v + T.A at hc
  have hB : T.B - T.A = b • v := by rw [hb]; abel
  have hC : T.C - T.A = c • v := by rw [hc]; abel
  apply T.noncollinear
  rw [hB, hC]
  simp only [Complexify.cross_def, QuadraticAlgebra.re_smul,
    QuadraticAlgebra.im_smul, smul_eq_mul]
  ring

/-- The ordered actual vertices form an affinely independent family over the surreal field. -/
theorem affineIndependent_vertices (T : Triangle.{u}) :
    AffineIndependent SignSequence.{u} ![T.A, T.B, T.C] :=
  affineIndependent_iff_not_collinear_set.mpr T.not_collinear

/-- The existing actual triangle, bundled as Mathlib's affine two-simplex. -/
def toAffine (T : Triangle.{u}) : Affine.Triangle SignSequence.{u} Surcomplex.{u} where
  points := ![T.A, T.B, T.C]
  independent := T.affineIndependent_vertices

@[simp] theorem toAffine_points_zero (T : Triangle.{u}) : T.toAffine.points 0 = T.A := rfl

@[simp] theorem toAffine_points_one (T : Triangle.{u}) : T.toAffine.points 1 = T.B := rfl

@[simp] theorem toAffine_points_two (T : Triangle.{u}) : T.toAffine.points 2 = T.C := rfl

end
end Surreal.Surcomplex.Triangle
