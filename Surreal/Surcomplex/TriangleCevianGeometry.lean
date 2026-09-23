import Surreal.Surcomplex.TriangleBisector
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-!
# Side parameters and actual cevian geometry

An interior point of the opposite side has a unique affine parameter.
Its two subtriangle determinants and its division ratio are explicit
in that parameter. This supplies the geometry for
`trigonometry:thm:cevian`, including uniqueness from a positive side
ratio, over the actual surreal and surcomplex carriers at every scale.
-/

universe u

namespace Surreal.Surcomplex.Triangle

open Foundations

noncomputable section

/-- The affine parameterization of the side from `B` to `C`. -/
def sidePoint (T : Triangle.{u}) (t : SignSequence.{u}) : Surcomplex.{u} :=
  AffineMap.lineMap T.B T.C t

/-- The side parameter is the weight of the terminal vertex. -/
theorem sidePoint_eq (T : Triangle.{u}) (t : SignSequence.{u}) :
    T.sidePoint t = (1 - t) • T.B + t • T.C :=
  AffineMap.lineMap_apply_module _ _ _

/-- A parameter strictly between zero and one gives an interior side point. -/
theorem sidePoint_mem_openSegment (T : Triangle.{u}) {t : SignSequence.{u}}
    (ht : t ∈ Set.Ioo 0 1) : T.sidePoint t ∈ openSegment SignSequence.{u} T.B T.C :=
  lineMap_mem_openSegment SignSequence.{u} T.B T.C ht

/-- Every interior side point, and only such a point, has an interior affine parameter. -/
theorem mem_openSegment_iff_exists_sidePoint (T : Triangle.{u}) (D : Surcomplex.{u}) :
    D ∈ openSegment SignSequence.{u} T.B T.C ↔
      ∃ t : SignSequence.{u}, t ∈ Set.Ioo 0 1 ∧ D = T.sidePoint t := by
  rw [openSegment_eq_image_lineMap]
  constructor
  · rintro ⟨t, ht, he⟩
    exact ⟨t, ht, he.symm⟩
  · rintro ⟨t, ht, he⟩
    exact ⟨t, ht, he.symm⟩

/-- Noncollinearity makes the side parameterization injective. -/
theorem sidePoint_injective (T : Triangle.{u}) : Function.Injective T.sidePoint :=
  AffineMap.lineMap_injective SignSequence.{u}
    (sub_ne_zero.mp (left_ne_zero_of_cross_ne_zero T.rotate.noncollinear)).symm

/-- The first subtriangle determinant is the side parameter times the whole determinant. -/
theorem cross_sidePoint_left (T : Triangle.{u}) (t : SignSequence.{u}) :
    Complexify.cross (T.B - T.A) (T.sidePoint t - T.A) =
      t * Complexify.cross (T.B - T.A) (T.C - T.A) := by
  simp only [sidePoint_eq, Complexify.cross_def, QuadraticAlgebra.re_sub,
    QuadraticAlgebra.im_sub, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add,
    QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, smul_eq_mul]
  ring

/-- The second subtriangle determinant is the complementary parameter times the whole one. -/
theorem cross_sidePoint_right (T : Triangle.{u}) (t : SignSequence.{u}) :
    Complexify.cross (T.sidePoint t - T.A) (T.C - T.A) =
      (1 - t) * Complexify.cross (T.B - T.A) (T.C - T.A) := by
  simp only [sidePoint_eq, Complexify.cross_def, QuadraticAlgebra.re_sub,
    QuadraticAlgebra.im_sub, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add,
    QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, smul_eq_mul]
  ring

/-- An interior parameter makes the first subtriangle noncollinear. -/
theorem sidePoint_cross_left_ne_zero (T : Triangle.{u}) {t : SignSequence.{u}}
    (ht : t ∈ Set.Ioo 0 1) :
    Complexify.cross (T.B - T.A) (T.sidePoint t - T.A) ≠ 0 := by
  rw [T.cross_sidePoint_left]
  exact mul_ne_zero ht.1.ne' T.noncollinear

/-- An interior parameter makes the second subtriangle noncollinear. -/
theorem sidePoint_cross_right_ne_zero (T : Triangle.{u}) {t : SignSequence.{u}}
    (ht : t ∈ Set.Ioo 0 1) :
    Complexify.cross (T.sidePoint t - T.A) (T.C - T.A) ≠ 0 := by
  rw [T.cross_sidePoint_right]
  exact mul_ne_zero (sub_pos.mpr ht.2).ne' T.noncollinear

/-- Every interior cevian point forms a noncollinear subtriangle with `AB`. -/
theorem cross_cevian_left_ne_zero (T : Triangle.{u}) (D : Surcomplex.{u})
    (hD : D ∈ openSegment SignSequence.{u} T.B T.C) :
    Complexify.cross (T.B - T.A) (D - T.A) ≠ 0 := by
  obtain ⟨t, ht, rfl⟩ := (T.mem_openSegment_iff_exists_sidePoint D).mp hD
  exact T.sidePoint_cross_left_ne_zero ht

/-- Every interior cevian point forms a noncollinear subtriangle with `AC`. -/
theorem cross_cevian_right_ne_zero (T : Triangle.{u}) (D : Surcomplex.{u})
    (hD : D ∈ openSegment SignSequence.{u} T.B T.C) :
    Complexify.cross (D - T.A) (T.C - T.A) ≠ 0 := by
  obtain ⟨t, ht, rfl⟩ := (T.mem_openSegment_iff_exists_sidePoint D).mp hD
  exact T.sidePoint_cross_right_ne_zero ht

/-- The first side displacement is the parameter times the whole side displacement. -/
theorem B_sub_sidePoint (T : Triangle.{u}) (t : SignSequence.{u}) :
    T.B - T.sidePoint t = t • (T.B - T.C) := by
  simp only [sidePoint_eq, sub_smul, one_smul, smul_sub]
  abel

/-- The second side displacement is the complementary parameter times the whole side. -/
theorem sidePoint_sub_C (T : Triangle.{u}) (t : SignSequence.{u}) :
    T.sidePoint t - T.C = (1 - t) • (T.B - T.C) := by
  simp only [sidePoint_eq, sub_smul, one_smul, smul_sub]
  abel

/-- The length from `B` to an interior parameter point is `t*a`. -/
theorem modulus_B_sub_sidePoint (T : Triangle.{u}) {t : SignSequence.{u}}
    (ht : t ∈ Set.Ioo 0 1) : modulus (T.B - T.sidePoint t) = t * T.sideA := by
  rw [T.B_sub_sidePoint]
  change Complexify.modulus (t • (T.B - T.C)) = t * Complexify.modulus (T.B - T.C)
  rw [Complexify.modulus_smul, abs_of_pos ht.1]

/-- The length from an interior parameter point to `C` is `(1-t)*a`. -/
theorem modulus_sidePoint_sub_C (T : Triangle.{u}) {t : SignSequence.{u}}
    (ht : t ∈ Set.Ioo 0 1) : modulus (T.sidePoint t - T.C) = (1 - t) * T.sideA := by
  rw [T.sidePoint_sub_C]
  change Complexify.modulus ((1 - t) • (T.B - T.C)) =
    (1 - t) * Complexify.modulus (T.B - T.C)
  rw [Complexify.modulus_smul, abs_of_pos (sub_pos.mpr ht.2)]

/-- The division ratio of an interior side point is the ratio of its two affine weights. -/
theorem sidePoint_side_ratio (T : Triangle.{u}) {t : SignSequence.{u}}
    (ht : t ∈ Set.Ioo 0 1) :
    modulus (T.B - T.sidePoint t) / modulus (T.sidePoint t - T.C) = t / (1 - t) := by
  rw [T.modulus_B_sub_sidePoint ht, T.modulus_sidePoint_sub_C ht]
  exact mul_div_mul_right _ _ T.sideA_pos.ne'

/-- The parameter ratio is injective on the open unit interval. -/
theorem side_parameter_ratio_injective :
    Set.InjOn (fun t : SignSequence.{u} => t / (1 - t)) (Set.Ioo 0 1) := by
  intro t ht u hu he
  have h := (div_eq_div_iff (sub_pos.mpr ht.2).ne' (sub_pos.mpr hu.2).ne').mp he
  nlinarith only [h]

/-- Equal division ratios determine the same actual interior side point. -/
theorem eq_of_side_ratio_eq (T : Triangle.{u}) (D E : Surcomplex.{u})
    (hD : D ∈ openSegment SignSequence.{u} T.B T.C)
    (hE : E ∈ openSegment SignSequence.{u} T.B T.C)
    (he : modulus (T.B - D) / modulus (D - T.C) =
      modulus (T.B - E) / modulus (E - T.C)) : D = E := by
  obtain ⟨t, ht, rfl⟩ := (T.mem_openSegment_iff_exists_sidePoint D).mp hD
  obtain ⟨u, hu, rfl⟩ := (T.mem_openSegment_iff_exists_sidePoint E).mp hE
  rw [T.sidePoint_side_ratio ht, T.sidePoint_side_ratio hu] at he
  exact congrArg T.sidePoint (side_parameter_ratio_injective ht hu he)

/-- Every positive actual surreal ratio determines exactly one interior side point. -/
theorem existsUnique_point_of_side_ratio (T : Triangle.{u}) (r : SignSequence.{u}) (hr : 0 < r) :
    ∃! D : Surcomplex.{u}, D ∈ openSegment SignSequence.{u} T.B T.C ∧
      modulus (T.B - D) / modulus (D - T.C) = r := by
  have hsum : 0 < 1 + r := add_pos zero_lt_one hr
  have ht : r / (1 + r) ∈ Set.Ioo (0 : SignSequence.{u}) 1 :=
    ⟨div_pos hr hsum, (div_lt_one hsum).mpr (by linarith only [hr])⟩
  have hratio : modulus (T.B - T.sidePoint (r / (1 + r))) /
      modulus (T.sidePoint (r / (1 + r)) - T.C) = r := by
    rw [T.sidePoint_side_ratio ht]
    field_simp [hsum.ne']
    ring
  refine ⟨T.sidePoint (r / (1 + r)), ⟨T.sidePoint_mem_openSegment ht, hratio⟩, ?_⟩
  rintro D ⟨hD, he⟩
  exact T.eq_of_side_ratio_eq D _ hD (T.sidePoint_mem_openSegment ht) (he.trans hratio.symm)

/-- The internal bisector point is characterized among side-interior points by ratio `c/b`. -/
theorem eq_bisectorPoint_of_side_ratio (T : Triangle.{u}) (D : Surcomplex.{u})
    (hD : D ∈ openSegment SignSequence.{u} T.B T.C)
    (he : modulus (T.B - D) / modulus (D - T.C) = T.sideC / T.sideB) :
    D = T.bisectorPoint :=
  T.eq_of_side_ratio_eq D T.bisectorPoint hD T.bisectorPoint_mem_openSegment
    (he.trans T.bisector_side_ratio.symm)

end
end Surreal.Surcomplex.Triangle
