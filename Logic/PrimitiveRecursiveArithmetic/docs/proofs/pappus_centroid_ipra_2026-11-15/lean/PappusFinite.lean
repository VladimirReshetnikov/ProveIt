import Mathlib

/-!
# Finite algebraic core of Pappus's centroid theorem

This file contains no `sorry` and isolates the identities that remain after
all geometric convergence obligations have been discharged:

* a revolved segment contributes `τ` times its radial first moment;
* an annular cylinder obtained from a rectangular cell contributes `τ` times
  its radial first moment;
* both identities are stable under finite list sums;
* after a nonzero length/area hypothesis, the first moment can be rewritten
  using the centroid quotient.

The nontrivial constructive geometry still to be formalized is the theorem
that the inner/outer regular-polygon frustum brackets converge to
`SegmentDatum.sweep`.  See `PappusRoadmap.lean` and `FORMALIZATION_PLAN.md`.
-/

namespace PappusFinite

open scoped BigOperators

section OrderedField

variable {K : Type*} [LinearOrderedField K]

/-- Data needed from one meridional segment after its length has been
constructed as a represented square root. -/
structure SegmentDatum (K : Type*) where
  r0 : K
  r1 : K
  length : K

namespace SegmentDatum

/-- Radial first moment of a uniform segment. -/
def moment (s : SegmentDatum K) : K := ((s.r0 + s.r1) / 2) * s.length

/-- The semantic swept area.  The frustum squeeze must justify this formula
from the polyhedral area brackets. -/
def sweep (τ : K) (s : SegmentDatum K) : K := τ * s.moment

@[simp] theorem sweep_eq_tau_mul_moment (τ : K) (s : SegmentDatum K) :
    s.sweep τ = τ * s.moment := rfl

end SegmentDatum

/-- Total polygonal length. -/
def polyLength (P : List (SegmentDatum K)) : K :=
  (P.map SegmentDatum.length).sum

/-- Total polygonal radial first moment. -/
def polyMoment (P : List (SegmentDatum K)) : K :=
  (P.map SegmentDatum.moment).sum

/-- Total swept area, counted with multiplicity. -/
def polySweep (τ : K) (P : List (SegmentDatum K)) : K :=
  (P.map (SegmentDatum.sweep τ)).sum

/-- Finite polygonal Pappus identity. -/
theorem polygon_pappus (τ : K) (P : List (SegmentDatum K)) :
    polySweep τ P = τ * polyMoment P := by
  induction P with
  | nil => simp [polySweep, polyMoment]
  | cons s P ih =>
      simp [polySweep, polyMoment, SegmentDatum.sweep, ih, mul_add]

/-- Radial coordinate of the polygonal line centroid. -/
def polygonCentroid (P : List (SegmentDatum K)) : K :=
  polyMoment P / polyLength P

/-- Centroid form of the finite polygonal theorem. -/
theorem polygon_pappus_centroid (τ : K) (P : List (SegmentDatum K))
    (hL : polyLength P ≠ 0) :
    polySweep τ P = τ * polyLength P * polygonCentroid P := by
  rw [polygon_pappus, polygonCentroid]
  field_simp [hL]
  <;> ring

/-- A rectangular cell `[a,b] × [c,d]` in the meridional half-plane. -/
structure CellDatum (K : Type*) where
  a : K
  b : K
  c : K
  d : K

namespace CellDatum

/-- Cell area. -/
def area (C : CellDatum K) : K := (C.b - C.a) * (C.d - C.c)

/-- Radial first moment of the cell. -/
def moment (C : CellDatum K) : K := ((C.a + C.b) / 2) * C.area

/-- Coefficient of `τ` in the annular-cylinder volume. -/
def shellCoeff (C : CellDatum K) : K :=
  ((C.b ^ 2 - C.a ^ 2) / 2) * (C.d - C.c)

/-- Annular-cylinder volume. -/
def volume (τ : K) (C : CellDatum K) : K := τ * C.shellCoeff

/-- The denominator-cleared one-cell identity. -/
theorem shellCoeff_eq_moment (C : CellDatum K) : C.shellCoeff = C.moment := by
  simp only [shellCoeff, moment, area]
  ring

/-- One-cell Pappus identity. -/
theorem volume_eq_tau_mul_moment (τ : K) (C : CellDatum K) :
    C.volume τ = τ * C.moment := by
  rw [volume, shellCoeff_eq_moment]

end CellDatum

/-- Area of a finite, interior-disjoint grid lamina. -/
def gridArea (G : List (CellDatum K)) : K :=
  (G.map CellDatum.area).sum

/-- Radial first moment of a finite grid lamina. -/
def gridMoment (G : List (CellDatum K)) : K :=
  (G.map CellDatum.moment).sum

/-- Swept volume of a finite grid lamina. -/
def gridVolume (τ : K) (G : List (CellDatum K)) : K :=
  (G.map (CellDatum.volume τ)).sum

/-- Finite grid-lamina Pappus identity. -/
theorem grid_pappus (τ : K) (G : List (CellDatum K)) :
    gridVolume τ G = τ * gridMoment G := by
  induction G with
  | nil => simp [gridVolume, gridMoment]
  | cons C G ih =>
      simp [gridVolume, gridMoment, CellDatum.volume_eq_tau_mul_moment,
        ih, mul_add]

/-- Radial coordinate of the grid-lamina centroid. -/
def gridCentroid (G : List (CellDatum K)) : K :=
  gridMoment G / gridArea G

/-- Centroid form of the finite volume theorem. -/
theorem grid_pappus_centroid (τ : K) (G : List (CellDatum K))
    (hA : gridArea G ≠ 0) :
    gridVolume τ G = τ * gridArea G * gridCentroid G := by
  rw [grid_pappus, gridCentroid]
  field_simp [hA]
  <;> ring

end OrderedField

section RationalExamples

/-- The sample polygon in the report has total length `8`. -/
example : (5 : ℚ) + 3 = 8 := by norm_num

/-- Its radial first moment is `49/2`. -/
example : ((1 + 4 : ℚ) / 2) * 5 + ((4 + 4 : ℚ) / 2) * 3 = 49 / 2 := by
  norm_num

/-- The sample L-shaped lamina has area `5` and moment `23/2`. -/
example :
    ((3 - 1 : ℚ) * (2 - 0) + (4 - 3) * (1 - 0) = 5) ∧
    (((1 + 3 : ℚ) / 2) * ((3 - 1) * (2 - 0)) +
      ((3 + 4 : ℚ) / 2) * ((4 - 3) * (1 - 0)) = 23 / 2) := by
  norm_num

end RationalExamples

end PappusFinite
