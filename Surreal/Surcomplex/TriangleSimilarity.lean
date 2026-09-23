import Surreal.Surcomplex.TriangleCongruence
import Surreal.Surcomplex.TriangleFromAngles

/-!
# Similarity and scale determination for actual triangles

Positive dilations are affine equivalences and multiply every actual
surreal distance by their scale. Side-side-side congruence then turns
proportional sides into a similarity. Equal angles give proportional
sides, and specifying one positive side uniquely determines the scale.
These complete the similarity clauses of `trigonometry:thm:sss`.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- Multiplication by a real scalar scales the determinant by its square. -/
theorem cross_ofReal_mul (k : SignSequence.{u}) (z w : Surcomplex.{u}) :
    Complexify.cross (ofReal k * z) (ofReal k * w) = k ^ 2 * Complexify.cross z w := by
  simp only [Complexify.cross_def, mul_re, mul_im, ofReal_re, ofReal_im,
    zero_mul, sub_zero, add_zero]
  ring

namespace Triangle

/-- Dilate all three vertices by an arbitrary positive actual surreal. -/
def scale (T : Triangle.{u}) (k : SignSequence.{u}) (hk : 0 < k) : Triangle.{u} where
  A := ofReal k * T.A
  B := ofReal k * T.B
  C := ofReal k * T.C
  noncollinear := by
    rw [← mul_sub, ← mul_sub, cross_ofReal_mul]
    exact mul_ne_zero (pow_ne_zero 2 hk.ne') T.noncollinear

@[simp] theorem sideA_scale (T : Triangle.{u}) (k : SignSequence.{u}) (hk : 0 < k) :
    (T.scale k hk).sideA = k * T.sideA := by
  change modulus (ofReal k * T.B - ofReal k * T.C) = _
  rw [← mul_sub, modulus_mul, modulus_ofReal, abs_of_pos hk]
  rfl

@[simp] theorem sideB_scale (T : Triangle.{u}) (k : SignSequence.{u}) (hk : 0 < k) :
    (T.scale k hk).sideB = k * T.sideB := by
  change modulus (ofReal k * T.C - ofReal k * T.A) = _
  rw [← mul_sub, modulus_mul, modulus_ofReal, abs_of_pos hk]
  rfl

@[simp] theorem sideC_scale (T : Triangle.{u}) (k : SignSequence.{u}) (hk : 0 < k) :
    (T.scale k hk).sideC = k * T.sideC := by
  change modulus (ofReal k * T.A - ofReal k * T.B) = _
  rw [← mul_sub, modulus_mul, modulus_ofReal, abs_of_pos hk]
  rfl

/-- Proportional side lengths are realized by an actual affine similarity of the whole plane. -/
theorem exists_similarity_of_sides_scaled (T U : Triangle.{u}) (k : SignSequence.{u})
    (hk : 0 < k) (hA : U.sideA = k * T.sideA) (hB : U.sideB = k * T.sideB)
    (hC : U.sideC = k * T.sideC) :
    ∃ f : Surcomplex.{u} ≃ᵃ[SignSequence.{u}] Surcomplex.{u},
      (∀ z w, modulus (f z - f w) = k * modulus (z - w)) ∧
        f T.A = U.A ∧ f T.B = U.B ∧ f T.C = U.C := by
  obtain ⟨g, hg, hgA, hgB, hgC⟩ := (T.scale k hk).exists_isometry_of_sides_eq U
    (by simpa only [sideA_scale] using hA.symm)
    (by simpa only [sideB_scale] using hB.symm)
    (by simpa only [sideC_scale] using hC.symm)
  let a : Surcomplex.{u}ˣ := Units.mk0 (ofReal k) ((map_ne_zero ofReal).mpr hk.ne')
  refine ⟨(mulAffineEquiv a).trans g, ?_, hgA, hgB, hgC⟩
  intro z w
  rw [AffineEquiv.trans_apply, AffineEquiv.trans_apply, hg, modulus_mulAffineEquiv_sub]
  change modulus (ofReal k) * modulus (z - w) = _
  rw [modulus_ofReal, abs_of_pos hk]

/-- Triangles with the same three actual angles are similar by an actual positive scale. -/
theorem exists_similarity_of_angles_eq (T U : Triangle.{u})
    (hA : T.angleA = U.angleA) (hB : T.angleB = U.angleB) (hC : T.angleC = U.angleC) :
    ∃ k : SignSequence.{u}, 0 < k ∧
      ∃ f : Surcomplex.{u} ≃ᵃ[SignSequence.{u}] Surcomplex.{u},
        (∀ z w, modulus (f z - f w) = k * modulus (z - w)) ∧
          f T.A = U.A ∧ f T.B = U.B ∧ f T.C = U.C := by
  obtain ⟨k, hk, hkA, hkB, hkC⟩ := U.exists_positive_side_scale_of_angles_eq T
    hA.symm hB.symm hC.symm
  exact ⟨k, hk, T.exists_similarity_of_sides_scaled U k hk hkA hkB hkC⟩

/-- Equal angles and one equal side fix the scale and hence give congruence. -/
theorem exists_isometry_of_angles_eq_of_sideA_eq (T U : Triangle.{u})
    (hA : T.angleA = U.angleA) (hB : T.angleB = U.angleB) (hC : T.angleC = U.angleC)
    (ha : T.sideA = U.sideA) :
    ∃ f : Surcomplex.{u} ≃ᵃ[SignSequence.{u}] Surcomplex.{u},
      PreservesModulus f ∧ f T.A = U.A ∧ f T.B = U.B ∧ f T.C = U.C := by
  obtain ⟨k, _, hkA, hkB, hkC⟩ := U.exists_positive_side_scale_of_angles_eq T
    hA.symm hB.symm hC.symm
  have hk : k = 1 := mul_right_cancel₀ T.sideA_pos.ne'
    (by simpa only [one_mul] using hkA.symm.trans ha.symm)
  rw [hk, one_mul] at hkB hkC
  exact T.exists_isometry_of_sides_eq U ha hkB.symm hkC.symm

end Triangle

/-- One positive side and its interior opposite angle determine exactly one positive sine scale. -/
theorem existsUnique_triangle_angle_scale (a : SignSequence.{u}) (ha : 0 < a)
    (α : SignSequence.FiniteElement.{u})
    (hα : α.val ∈ Set.Ioo 0 (SignSequence.ofReal Real.pi)) :
    ∃! k : SignSequence.{u}, 0 < k ∧ a = k * finiteSin α := by
  have hs := finiteSin_pos_of_mem_Ioo α hα
  refine ⟨a / finiteSin α, ⟨div_pos ha hs, (div_mul_cancel₀ a hs.ne').symm⟩, ?_⟩
  rintro k ⟨_, he⟩
  exact (eq_div_iff hs.ne').mpr he.symm

end
end Surreal.Surcomplex
