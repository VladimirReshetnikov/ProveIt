import Surreal.Surcomplex.TriangleCevianGeometry
import Surreal.Surcomplex.CevianSineMonotonicity

/-!
# Actual cevian sine ratios and the unique internal bisector

Every point strictly inside an actual triangle side cuts two
noncollinear subtriangles. Their positive interior angles and determinant
formulas give `trigonometry:thm:cevian` and `trigonometry:eq:cevian`.
The prescribed side ratio characterizes the internal bisector uniquely.
-/

universe u

namespace Surreal.Surcomplex.Triangle

open Foundations

noncomputable section

/-- The angle BAD cut off by an interior trace on BC. -/
def cevianAngleLeft (T : Triangle.{u}) (D : Surcomplex.{u})
    (hD : D ∈ openSegment SignSequence.{u} T.B T.C) : SignSequence.FiniteElement.{u} :=
  interiorAngle (T.B - T.A) (D - T.A) (T.cross_cevian_left_ne_zero D hD)

/-- The angle DAC cut off by an interior trace on BC. -/
def cevianAngleRight (T : Triangle.{u}) (D : Surcomplex.{u})
    (hD : D ∈ openSegment SignSequence.{u} T.B T.C) : SignSequence.FiniteElement.{u} :=
  interiorAngle (D - T.A) (T.C - T.A) (T.cross_cevian_right_ne_zero D hD)

theorem cevianAngleLeft_mem (T : Triangle.{u}) (D : Surcomplex.{u})
    (hD : D ∈ openSegment SignSequence.{u} T.B T.C) :
    (T.cevianAngleLeft D hD).val ∈ Set.Ioo 0 (SignSequence.ofReal Real.pi) :=
  interiorAngle_mem _ _ _

theorem cevianAngleRight_mem (T : Triangle.{u}) (D : Surcomplex.{u})
    (hD : D ∈ openSegment SignSequence.{u} T.B T.C) :
    (T.cevianAngleRight D hD).val ∈ Set.Ioo 0 (SignSequence.ofReal Real.pi) :=
  interiorAngle_mem _ _ _

theorem sin_cevianAngleLeft_pos (T : Triangle.{u}) (D : Surcomplex.{u})
    (hD : D ∈ openSegment SignSequence.{u} T.B T.C) :
    0 < finiteSin (T.cevianAngleLeft D hD) :=
  finiteSin_pos_of_mem_Ioo _ (T.cevianAngleLeft_mem D hD)

theorem sin_cevianAngleRight_pos (T : Triangle.{u}) (D : Surcomplex.{u})
    (hD : D ∈ openSegment SignSequence.{u} T.B T.C) :
    0 < finiteSin (T.cevianAngleRight D hD) :=
  finiteSin_pos_of_mem_Ioo _ (T.cevianAngleRight_mem D hD)

/-- The two subtriangle areas have exactly the ratio of their bases on the opposite side. -/
theorem cevian_area_ratio (T : Triangle.{u}) (D : Surcomplex.{u})
    (hD : D ∈ openSegment SignSequence.{u} T.B T.C) :
    triangleArea (T.B - T.A) (D - T.A) / triangleArea (D - T.A) (T.C - T.A) =
      modulus (T.B - D) / modulus (D - T.C) := by
  obtain ⟨t, ht, rfl⟩ := (T.mem_openSegment_iff_exists_sidePoint D).mp hD
  rw [T.sidePoint_side_ratio ht]
  change (|Complexify.cross (T.B - T.A) (T.sidePoint t - T.A)| / 2) /
    (|Complexify.cross (T.sidePoint t - T.A) (T.C - T.A)| / 2) = t / (1 - t)
  rw [T.cross_sidePoint_left, T.cross_sidePoint_right, abs_mul, abs_mul,
    abs_of_pos ht.1, abs_of_pos (sub_pos.mpr ht.2)]
  field_simp [(abs_pos.mpr T.noncollinear).ne', (sub_pos.mpr ht.2).ne']

/-- The ratio of the side pieces is the adjacent-side-weighted ratio of the split sines. -/
theorem cevian_sine_ratio (T : Triangle.{u}) (D : Surcomplex.{u})
    (hD : D ∈ openSegment SignSequence.{u} T.B T.C) :
    modulus (T.B - D) / modulus (D - T.C) =
      T.sideC * finiteSin (T.cevianAngleLeft D hD) /
        (T.sideB * finiteSin (T.cevianAngleRight D hD)) := by
  obtain ⟨t, ht, rfl⟩ := (T.mem_openSegment_iff_exists_sidePoint D).mp hD
  have hm : modulus (T.sidePoint t - T.A) ≠ 0 :=
    (modulus_pos (right_ne_zero_of_cross_ne_zero (T.sidePoint_cross_left_ne_zero ht))).ne'
  have hc : |Complexify.cross (T.B - T.A) (T.C - T.A)| ≠ 0 :=
    (abs_pos.mpr T.noncollinear).ne'
  rw [T.sidePoint_side_ratio ht]
  simp only [cevianAngleLeft, cevianAngleRight, finiteSin_interiorAngle,
    T.cross_sidePoint_left, T.cross_sidePoint_right,
    abs_mul, abs_of_pos ht.1, abs_of_pos (sub_pos.mpr ht.2),
    modulus_sub_comm T.B T.A]
  change t / (1 - t) =
    T.sideC * (t * |Complexify.cross (T.B - T.A) (T.C - T.A)| /
      (T.sideC * modulus (T.sidePoint t - T.A))) /
    (T.sideB * ((1 - t) * |Complexify.cross (T.B - T.A) (T.C - T.A)| /
      (modulus (T.sidePoint t - T.A) * T.sideB)))
  field_simp [T.sideB_pos.ne', T.sideC_pos.ne', hm, hc, (sub_pos.mpr ht.2).ne']

/-- Equality of the two actual subangles is equivalent to the internal-bisector side ratio. -/
theorem cevian_angles_eq_iff_side_ratio (T : Triangle.{u}) (D : Surcomplex.{u})
    (hD : D ∈ openSegment SignSequence.{u} T.B T.C) :
    T.cevianAngleLeft D hD = T.cevianAngleRight D hD ↔
      modulus (T.B - D) / modulus (D - T.C) = T.sideC / T.sideB := by
  constructor
  · intro he
    rw [T.cevian_sine_ratio D hD, he]
    field_simp [T.sideB_pos.ne', (T.sin_cevianAngleRight_pos D hD).ne']
  · intro hr
    have hp := T.eq_bisectorPoint_of_side_ratio D hD hr
    subst D
    exact T.bisector_angle_left.trans T.bisector_angle_right.symm

/-- There is exactly one interior trace whose cevian bisects the actual interior angle. -/
theorem cevian_angles_eq_iff_eq_bisectorPoint (T : Triangle.{u}) (D : Surcomplex.{u})
    (hD : D ∈ openSegment SignSequence.{u} T.B T.C) :
    T.cevianAngleLeft D hD = T.cevianAngleRight D hD ↔ D = T.bisectorPoint := by
  rw [T.cevian_angles_eq_iff_side_ratio D hD]
  constructor
  · exact T.eq_bisectorPoint_of_side_ratio D hD
  · rintro rfl
    exact T.bisector_side_ratio

end
end Surreal.Surcomplex.Triangle
