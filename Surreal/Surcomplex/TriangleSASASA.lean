import Surreal.Surcomplex.TriangleSimilarity

/-!
# Side-angle-side and angle-side-angle triangle reconstruction

The reconstruction paragraph following `trigonometry:thm:sss` gives
side-angle-side and angle-side-angle existence and congruence. These
results use the actual finite interior angles and arbitrary positive
surreal side lengths. Congruence is witnessed by an affine equivalence
of the actual surcomplex plane preserving every surreal-valued distance.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

namespace Triangle

/-- Two equal adjacent sides and their equal included angle determine congruent triangles. -/
theorem exists_isometry_of_sas (T U : Triangle.{u})
    (hA : T.angleA = U.angleA) (hb : T.sideB = U.sideB) (hc : T.sideC = U.sideC) :
    ∃ f : Surcomplex.{u} ≃ᵃ[SignSequence.{u}] Surcomplex.{u},
      PreservesModulus f ∧ f T.A = U.A ∧ f T.B = U.B ∧ f T.C = U.C := by
  have ha : T.sideA = U.sideA := by
    apply (sq_eq_sq₀ T.sideA_pos.le U.sideA_pos.le).mp
    rw [T.cosine_law, U.cosine_law, hA, hb, hc]
  exact T.exists_isometry_of_sides_eq U ha hb hc

/-- Two equal angles and their equal included side determine congruent triangles. -/
theorem exists_isometry_of_asa (T U : Triangle.{u})
    (hA : T.angleA = U.angleA) (hB : T.angleB = U.angleB) (hc : T.sideC = U.sideC) :
    ∃ f : Surcomplex.{u} ≃ᵃ[SignSequence.{u}] Surcomplex.{u},
      PreservesModulus f ∧ f T.A = U.A ∧ f T.B = U.B ∧ f T.C = U.C := by
  have ht := T.angle_sum
  rw [hA, hB] at ht
  have hC : T.angleC = U.angleC := add_left_cancel (ht.trans U.angle_sum.symm)
  obtain ⟨f, hf, hfC, hfA, hfB⟩ :=
    T.rotate.rotate.exists_isometry_of_angles_eq_of_sideA_eq U.rotate.rotate
      (by simpa only [angleA_rotate, angleB_rotate] using hC)
      (by simpa only [angleB_rotate, angleC_rotate] using hA)
      (by simpa only [angleC_rotate, angleA_rotate] using hB)
      (by simpa only [sideA_rotate, sideB_rotate] using hc)
  exact ⟨f, hf, hfA, hfB, hfC⟩

end Triangle

/-- Any two positive sides and an interior included angle have a noncollinear realization. -/
theorem exists_triangle_of_sas (b c : SignSequence.{u}) (hb : 0 < b) (hc : 0 < c)
    (α : SignSequence.FiniteElement.{u})
    (hα : α.val ∈ Set.Ioo 0 (SignSequence.ofReal Real.pi)) :
    ∃ T : Triangle.{u}, T.angleA = α ∧ T.sideB = b ∧ T.sideC = c := by
  obtain ⟨T, hB, hC, hA⟩ := exists_triangle_of_included_angle b c hb hc α hα
  exact ⟨T, hA, hB, hC⟩

/-- Two positive angles summing below pi and a positive included side have a realization. -/
theorem exists_triangle_of_asa (α β : SignSequence.FiniteElement.{u})
    (hα : 0 < α.val) (hβ : 0 < β.val)
    (hs : α.val + β.val < SignSequence.ofReal Real.pi)
    (c : SignSequence.{u}) (hc : 0 < c) :
    ∃ T : Triangle.{u}, T.angleA = α ∧ T.angleB = β ∧ T.sideC = c := by
  let γ : SignSequence.FiniteElement.{u} := SignSequence.finiteOfReal Real.pi - (α + β)
  have hγval : γ.val = SignSequence.ofReal Real.pi - (α.val + β.val) := rfl
  have hγ : 0 < γ.val := by rw [hγval]; exact sub_pos.mpr hs
  have hγmem : γ.val ∈ Set.Ioo 0 (SignSequence.ofReal Real.pi) := by
    refine ⟨hγ, ?_⟩
    rw [hγval]
    linarith only [hα, hβ]
  have hsum : α + β + γ = SignSequence.finiteOfReal Real.pi := by
    dsimp only [γ]
    abel
  have hsin : 0 < finiteSin γ := finiteSin_pos_of_mem_Ioo γ hγmem
  obtain ⟨T, hA, hB, _, _, _, hC⟩ :=
    exists_triangle_of_angles α β γ hα hβ hγ hsum (c / finiteSin γ) (div_pos hc hsin)
  refine ⟨T, hA, hB, ?_⟩
  rwa [div_mul_cancel₀ c hsin.ne'] at hC

end
end Surreal.Surcomplex
