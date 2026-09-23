import Surreal.Surcomplex.PlaneIsometry
import Surreal.Surcomplex.TriangleFromSides

/-!
# Side-side-side congruence in the actual surcomplex plane

Normalize each triangle's first edge by a translation and rotation.
Equal side lengths force the remaining vertices to be equal or conjugate.
Composing the normalizations, and a reflection in the second case, yields
a Mathlib affine equivalence preserving every actual surreal distance.
This proves the Euclidean congruence clause of `trigonometry:thm:sss`.
-/

universe u

namespace Surreal.Surcomplex.Triangle

open Foundations

noncomputable section

/-- Equal side data is realized by an actual affine isometry matching all corresponding vertices. -/
theorem exists_isometry_of_sides_eq (T U : Triangle.{u})
    (hA : T.sideA = U.sideA) (hB : T.sideB = U.sideB) (hC : T.sideC = U.sideC) :
    ∃ f : Surcomplex.{u} ≃ᵃ[SignSequence.{u}] Surcomplex.{u},
      PreservesModulus f ∧ f T.A = U.A ∧ f T.B = U.B ∧ f T.C = U.C := by
  obtain ⟨f, hfA, hfB, hf⟩ := exists_normalizing_affineEquiv T.A T.B
    (sub_ne_zero.mp (left_ne_zero_of_cross_ne_zero T.noncollinear)).symm
  obtain ⟨g, hgA, hgB, hg⟩ := exists_normalizing_affineEquiv U.A U.B
    (sub_ne_zero.mp (left_ne_zero_of_cross_ne_zero U.noncollinear)).symm
  have hfB' : f T.B = ofReal T.sideC := by
    simpa only [sideC, modulus_sub_comm T.B T.A] using hfB
  have hgB' : g U.B = ofReal U.sideC := by
    simpa only [sideC, modulus_sub_comm U.B U.A] using hgB
  have hp0 : modulus (f T.C) = T.sideB := by
    have he := hf T.C T.A
    simpa only [hfA, sub_zero, sideB] using he
  have hq0 : modulus (g U.C) = U.sideB := by
    have he := hg U.C U.A
    simpa only [hgA, sub_zero, sideB] using he
  have hpc : modulus (f T.C - ofReal T.sideC) = T.sideA := by
    have he := hf T.C T.B
    simpa only [hfB', sideA, modulus_sub_comm T.C T.B] using he
  have hqc : modulus (g U.C - ofReal U.sideC) = U.sideA := by
    have he := hg U.C U.B
    simpa only [hgB', sideA, modulus_sub_comm U.C U.B] using he
  have he := Complexify.normalized_point_eq_or_eq_conj T.sideC T.sideC_pos.ne'
    (f T.C) (g U.C) (hp0.trans (hB.trans hq0.symm))
    (by change modulus (f T.C - ofReal T.sideC) = modulus (g U.C - ofReal T.sideC)
        rw [hpc, hC, hqc, hA])
  change f T.C = g U.C ∨ f T.C = conj (g U.C) at he
  rcases he with he | he
  · refine ⟨f.trans g.symm, hf.trans hg.symm, ?_, ?_, ?_⟩
    · simp only [AffineEquiv.trans_apply, hfA, ← hgA, AffineEquiv.symm_apply_apply]
    · simp only [AffineEquiv.trans_apply, hfB', hC, ← hgB', AffineEquiv.symm_apply_apply]
    · simp only [AffineEquiv.trans_apply, he, AffineEquiv.symm_apply_apply]
  · refine ⟨(f.trans conjAffineEquiv).trans g.symm,
      (hf.trans preservesModulus_conj).trans hg.symm, ?_, ?_, ?_⟩
    · simp only [AffineEquiv.trans_apply, conjAffineEquiv_apply, hfA, map_zero]
      rw [← hgA, AffineEquiv.symm_apply_apply]
    · simp only [AffineEquiv.trans_apply, conjAffineEquiv_apply, hfB', conj_ofReal, hC]
      rw [← hgB', AffineEquiv.symm_apply_apply]
    · simp only [AffineEquiv.trans_apply, conjAffineEquiv_apply, he, conj_conj,
        AffineEquiv.symm_apply_apply]

/-- Any affine isometry carrying the vertices preserves all corresponding side lengths. -/
theorem sides_eq_of_isometry (T U : Triangle.{u})
    (f : Surcomplex.{u} ≃ᵃ[SignSequence.{u}] Surcomplex.{u}) (hf : PreservesModulus f)
    (hA : f T.A = U.A) (hB : f T.B = U.B) (hC : f T.C = U.C) :
    T.sideA = U.sideA ∧ T.sideB = U.sideB ∧ T.sideC = U.sideC := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hB, hC, sideA] using (hf T.B T.C).symm
  · simpa only [hC, hA, sideB] using (hf T.C T.A).symm
  · simpa only [hA, hB, sideC] using (hf T.A T.B).symm

/-- Equality of all three sides is exactly Euclidean congruence by an actual affine isometry. -/
theorem sides_eq_iff_exists_isometry (T U : Triangle.{u}) :
    (T.sideA = U.sideA ∧ T.sideB = U.sideB ∧ T.sideC = U.sideC) ↔
      ∃ f : Surcomplex.{u} ≃ᵃ[SignSequence.{u}] Surcomplex.{u},
        PreservesModulus f ∧ f T.A = U.A ∧ f T.B = U.B ∧ f T.C = U.C := by
  constructor
  · rintro ⟨hA, hB, hC⟩
    exact T.exists_isometry_of_sides_eq U hA hB hC
  · rintro ⟨f, hf, hA, hB, hC⟩
    exact T.sides_eq_of_isometry U f hf hA hB hC

end
end Surreal.Surcomplex.Triangle
